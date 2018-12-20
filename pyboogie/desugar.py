# Types
from .ast import AstIntType, AstBoolType, AstBVType, AstMapType, AstCompoundType
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
from typing import Union, Tuple, Optional, Any, Dict, Iterable, Generic, TypeVar, List
from .util import get_uid, ccast

def desugarExpr(e: AstExpr) -> AstExpr:
    assert False, "NYI"

def desugarStmt(s: AstStmt) -> List[AstStmt]:
    if (isinstance(s, AstLabel)):
        desugared = desugarStmt(s.stmt)
        t : List[AstStmt] = [AstLabel(s.label, desugared[0])] 
        return t + desugared[1:]
    elif (isinstance(s, AstOneExprStmt)):
        return [AstOneExprStmt(desugarExpr(s.expr))]
    elif (isinstance(s, AstAssignment)):
        assert False, "NYI desugar map updates? Needs thinking"
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

        thenBlock : List[AstStmt] = [ AstLabel(thenLbl, AstAssume(cond)) ]
        thenBlock += s.thenS
        thenBlock += [ AstGoto([unionLbl]) ]

        elseBlock : List[AstStmt] = [ AstLabel(elseLbl, AstAssume(AstUnExpr("!", cond))) ]
        if isinstance(s.elseS, AstStmt):
            elseBlock += desugarStmt(s.elseS) 
        else:
            elseBlock += ccast(s.elseS, List[AstStmt])

        elseBlock += [ AstGoto([unionLbl]) ]

        unionBlock : List[AstStmt] = [ AstLabel(unionLbl, AstAssert(AstTrue())) ]
        return thenBlock + elseBlock + unionBlock 


def desugarDecl(d: AstDecl) -> AstDecl:
    if (isinstance(d, AstVarDecl) or
        isinstance(d, AstConstDecl) or
        isinstance(d, AstTypeConstructorDecl)):
        return d
    elif (isinstance(d, AstFunctionDecl)):
        newExpr: Optional[AstExpr] = None if d.body is None else desugarExpr(d.body)

        return AstFunctionDecl(d.attributes, d.id, d.parameters, d.returns,
                newExpr)
    elif (isinstance(d, AstAxiomDecl)):
        return AstAxiomDecl(d.attributes, desugarExpr(d.expr)) 
    elif (isinstance(d, AstImplementation)):
        return AstImplementation(d.name, d.parameters, d.returns,
            AstBody(d.body.bindings, [desugarStmt(s) for s in d.body.stmts]))
    elif (isinstance(d, AstProcedure)):
        newBody: Optional[AstBody] = None if d.body is None else\
            AstBody(d.body.bindings, [desugarStmt(s) for s in d.body.stmts])

        return AstProcedure(d.attributes, d.name, d.parameters, d.returns,
            [(isFree, desugarExpr(expr)) for (isFree, expr) in d.requires],
            [(isFree, desugarExpr(expr)) for (isFree, expr) in d.ensures],
            d.modifies,
            newBody)
    else:
        assert False, "NYI desugaring of decl {}".format(d)

def desugar(p: AstProgram) -> AstProgram:
    return AstProgram([desugarDecl(d) for d in p.decls])
