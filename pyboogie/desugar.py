# Types
from .ast import AstIntType, AstBoolType, AstBVType, AstMapType, \
        AstCompoundType
# Expressions
from .ast import AstExpr, AstFalse, AstTrue, AstNumber, AstId, AstWildcard,\
        AstMapIndex, AstMapUpdate, AstUnExpr, AstBinExpr, AstTernary,\
        AstForallExpr, AstFuncExpr
# Statements
from .ast import AstStmt, AstLabel, AstOneExprStmt, AstAssignment, \
        AstHavoc, AstReturn, AstGoto, AstCall, AstAssume, AstAssert, AstIf
# Declarations
from .ast import AstProgram, AstProcedure, AstFunctionDecl, AstImplementation,\
        AstDecl, AstBinding, AstNode, AstType, AstTypeConstructorDecl, \
        AstBody, AstVarDecl, AstConstDecl, AstAxiomDecl
from typing import Union, Tuple, Optional, Any, Dict, Iterable, Generic, \
        TypeVar, List, cast
from .util import get_uid, ccast, flattenList


def desugarExpr(e: AstExpr) -> AstExpr:
    return e


def desugarStmt(s: AstStmt) -> List[AstStmt]:
    if (isinstance(s, AstLabel)):
        desugared = desugarStmt(s.stmt)
        t: List[AstStmt] = [AstLabel(s.label, desugared[0])]
        return t + desugared[1:]
    elif (isinstance(s, AstOneExprStmt)):
        return [s.__class__(desugarExpr(s.expr))]
    elif (isinstance(s, AstAssignment)):
        """ Rewrite all assignments of the form:
            a[i] := v;
            to:
            a = a[i:=v];

            This applies to multi-dimensional maps:
            a[i][j] := v;
            to:
            a = a[i:=a[i][j:=v]]
        """
        lhsL: List[Union[AstId, AstMapIndex]] = []
        rhsL: List[AstExpr] = []

        for (lhs, rhs) in zip(s.lhs, s.rhs):
            while (isinstance(lhs, AstMapIndex)):
                rhs = AstMapUpdate(lhs.map, lhs.index, rhs)
                assert (isinstance(lhs.map, AstMapIndex) or
                        isinstance(lhs.map, AstId))
                lhs = lhs.map

            assert isinstance(lhs, AstId)
            lhsL.append(lhs)
            rhsL.append(desugarExpr(rhs))

        return [AstAssignment(lhsL, rhsL)]
    elif (isinstance(s, AstHavoc) or isinstance(s, AstGoto) or
          isinstance(s, AstReturn)):
        return [s]
    elif (isinstance(s, AstCall)):
        return [AstCall(s.attributes, s.lhs, s.id,
                        [desugarExpr(arg) for arg in s.arguments])]
    elif (isinstance(s, AstCall)):
        return [AstCall(s.attributes, s.lhs, s.id,
                        [desugarExpr(arg) for arg in s.arguments])]
    elif (isinstance(s, AstIf)):
        thenLbl = get_uid("_then_")
        elseLbl = get_uid("_else_")
        unionLbl = get_uid("_union_")

        cond = desugarExpr(s.condition)
        if (s.elseS is not None):
            beforeIf: List[AstStmt] = [ AstGoto([thenLbl, elseLbl])]
        else:
            beforeIf = [ AstGoto([thenLbl, unionLbl])]

        thenBlock: List[AstStmt] = [AstLabel(thenLbl, AstAssume(desugarExpr(cond)))]
        thenBlock += flattenList(map(desugarStmt, s.thenS))
        thenBlock += [AstGoto([unionLbl])]

        if (s.elseS is not None):
            elseBlock: List[AstStmt] = [
                AstLabel(elseLbl, AstAssume(AstUnExpr("!", cond)))
            ]
            if isinstance(s.elseS, AstStmt):
                elseBlock += desugarStmt(s.elseS)
            else:
                elseBlock += flattenList(map(desugarStmt, cast(List[AstStmt], s.elseS)))

            elseBlock += [AstGoto([unionLbl])]
        else:
            elseBlock = []

        unionBlock: List[AstStmt] = [AstLabel(unionLbl, AstAssert(AstTrue()))]
        return beforeIf + thenBlock + elseBlock + unionBlock
    else:
        assert False, "NYI desugar {}".format(s)


def addEntry(stmts: List[AstStmt]) -> List[AstStmt]:
    if not isinstance(stmts[0], AstLabel):
        stmts[0] = AstLabel("__entry__", stmts[0])
    return stmts


def desugarDecl(d: AstDecl) -> AstDecl:
    if (isinstance(d, AstVarDecl) or
        isinstance(d, AstConstDecl) or
        isinstance(d, AstTypeConstructorDecl)):
        # TODO: Update after where statements added
        return d
    elif (isinstance(d, AstFunctionDecl)):
        if (d.body is None):
            newExpr: Optional[AstExpr] = None
        else:
            newExpr = desugarExpr(d.body)

        return AstFunctionDecl(
            d.attributes,
            d.id,
            d.parameters,
            d.returns,
            newExpr)
    elif (isinstance(d, AstAxiomDecl)):
        return AstAxiomDecl(d.attributes, desugarExpr(d.expr))
    elif (isinstance(d, AstImplementation)):
        return AstImplementation(
            d.name,
            d.parameters,
            d.returns,
            AstBody(d.body.bindings, addEntry(flattenList([desugarStmt(s) for s in d.body.stmts]))))
    elif (isinstance(d, AstProcedure)):
        if (d.body is None):
            newBody: Optional[AstBody] = None
        else:
            newBody = AstBody(
                    d.body.bindings,
                    addEntry(flattenList([desugarStmt(s) for s in d.body.stmts])))

        return AstProcedure(
            d.attributes,
            d.name,
            d.parameters,
            d.returns,
            [(isFree, desugarExpr(expr)) for (isFree, expr) in d.requires],
            [(isFree, desugarExpr(expr)) for (isFree, expr) in d.ensures],
            d.modifies,
            newBody)
    else:
        assert False, "NYI desugaring of decl {}".format(d)


def desugar(p: AstProgram) -> AstProgram:
    return AstProgram([desugarDecl(d) for d in p.decls])
