#pylint: disable=no-self-argument,unused-argument, multiple-statements
from typing import Any, TypeVar, Iterable, Union, Generic
from pyparsing import delimitedList,nums, ParserElement, operatorPrecedence, \
        opAssoc, StringEnd, ParseResults, restOfLine
from pyparsing import ZeroOrMore as ZoM,\
    OneOrMore as OoM,\
    Keyword as K,\
    Suppress as S,\
    Literal as L,\
    Forward as F,\
    Optional as O,\
    Regex as R,\
    Word as W,\
    Group as G

T=TypeVar("T")

ParserElement.enablePackrat()
csl = delimitedList

class BoogieParser(Generic[T]):
  # Statements
  def onAssert(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onAssume(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onReturn(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onGoto(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onAssignment(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onHavoc(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onCallAssignStmt(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onProgram(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onVarDecl(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onAxiomDecl(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onConstDecl(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onImplementationDecl(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onProcedureDecl(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onTypeConstructorDecl(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onBody(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onLocalVarDecl(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onPrimitiveType(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onMapType(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onCompoundType(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onType(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onLabeledStatement(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onMapIndexArgs(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onMapUpdateArgs(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onFunAppArgs(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onQuantified(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onBinding(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onAttribute(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onAtom(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onUnaryOp(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onLABinOp(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onRABinOp(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")
  def onNABinOp(s, prod: "ParserElement[T]", st: str, loc: int, toks:"ParseResults[T]") -> "Iterable[T]": raise Exception("NYI")

  def __init__(s) -> None:
    s.LT = L("<")
    s.GT = L(">")
    s.EQ = L("=")
    # Braces/Brackets
    s.LSQBR = S("[")
    s.RSQBR = S("]")
    s.LPARN = S("(")
    s.RPARN = S(")")
    s.LBRAC = S("{")
    s.RBRAC = S("}")
    # Various Delimiters
    s.SEMI = S(";")
    s.COLN = S(":")
    s.ASSGN = S(":=")
    s.STAR = S("*")

    ####### Keywords
    s.INT = K("int")
    s.BOOL = K("bool")
    s.TYPE = K("type")
    s.FINITE = K("finite")
    s.CONST = K("const")
    s.UNIQUE = K("unique")
    s.RETURNS = K("returns")
    s.FUNCTION = K("function")
    s.FALSE = K("false") # type: ParserElement[T]
    s.FALSE.setParseAction(\
            lambda st, loc, toks:  s.onAtom(s.FALSE, st, loc, toks))
    s.TRUE = K("true") # type: ParserElement[T]
    s.TRUE.setParseAction(\
            lambda st, loc, toks:  s.onAtom(s.TRUE, st, loc, toks))
    s.OLD = K("old")
    s.AXIOM = K("axiom")
    s.FORALL = K("forall")
    s.EXISTS = K("exists")
    s.VAR = K("var")
    s.PROCEDURE = K("procedure")
    s.FREE = K("free")
    s.RETURNS = K("returns")
    s.REQUIRES = K("requires")
    s.MODIFIES = K("modifies")
    s.ENSURES = K("ensures")
    s.ASSERT = K("assert")
    s.COMPLETE = K("complete")
    s.UNIQUE = K("unique")
    s.IF = K("if")
    s.ELSE = K("else")
    s.FREE = K("free")
    s.INVARIANT = K("invariant")
    s.ASSUME = K("assume")
    s.ASSERT = K("assert")
    s.HAVOC = K("havoc")
    s.CALL = K("call")
    s.WHILE = K("while")
    s.BREAK = K("break")
    s.GOTO = K("goto")
    s.RETURN = K("return")
    s.IMPLEMENTATION = K("implementation")

    s.Id = R("[a-zA-Z_#.$'`~^?\\\\][a-zA-Z0-9_#.$'`~^?\\\\]*") # type: ParserElement[T]
    s.Id.setParseAction(lambda st, loc, toks:  s.onAtom(s.Id, st, loc, toks))
    s.ParentEdge = O(s.UNIQUE) + s.Id
    s.ParentInfo = S("<:") + csl(s.ParentEdge)
    s.OrderSpec = O(s.ParentInfo) + O(s.COMPLETE)
    s.StringLiteral = S(L("\"")) + R("[^\"]*") + S(L("\""))
    s.Trigger = F(); # TODO

    ####### Expressions
    s.EquivOp = L("<==>")
    s.ImplOp = L("==>")
    s.OrOp = L("||")
    s.AndOp = L("&&")
    s.AndOrOp = s.AndOp | s.OrOp
    s.RelOp = (L("!=") | L ("<=") | L(">=") | L("<:") \
               | L("==") |  L("<") | L(">") )
    s.ConcatOp = L("++")
    s.AddOp = (L("+") | L("-"))
    s.MulOp = (L("*") | L("/") | L("div") | L("mod"))
    s.UnOp = (L("!") | L("-"))
    s.ArithUnOp = L("-")
    s.BoolUnOp = L("!")
    s.QOp = (s.FORALL | s.EXISTS)
    s.QSep = L("::")

    s.Expr = F() # type: ParserElement[T]

    ####### Attributes
    s.AttrArg = s.Expr | s.StringLiteral
    s.Attribute = S(s.LBRAC) + S(s.COLN) + s.Id + G(O(csl(s.AttrArg))) + S(s.RBRAC)
    s.Attribute.setParseAction(lambda st, loc, toks: s.onAttribute(s.Attribute, st, loc, toks))
    s.AttrList = ZoM(s.Attribute)

    ####### Types
    s.Type = F() # type: ParserElement[T]
    s.BVType = R("bv[0-9][0-9]*")
    s.INT.setParseAction(lambda st, loc, toks: s.onPrimitiveType(s.INT, st, loc, toks))
    s.BOOL.setParseAction(lambda st, loc, toks: s.onPrimitiveType(s.BOOL, st, loc, toks))
    s.BVType.setParseAction(lambda st, loc, toks: s.onPrimitiveType(s.BVType, st, loc, toks))

    s.TypeAtom = s.INT | s.BOOL | s.BVType | S(s.LPARN) + s.Type + S(s.RPARN)
    s.TypeArgs = S(s.LT) + csl(s.Id) + S(s.GT)
    s.MapType = G(O(s.TypeArgs)) + S(s.LSQBR) + G(csl(s.Type)) + S(s.RSQBR) + s.Type
    s.MapType.setParseAction(lambda st, loc, toks: s.onMapType(s.Type, st, loc, toks))

    s.TypeCtorArgs = F()
    s.TypeCtorArgs << (s.TypeAtom + O(s.TypeCtorArgs)\
                   | s.Id + O(s.TypeCtorArgs)\
                   | s.MapType)

    s.CompoundType = s.Id + O(s.TypeCtorArgs)
    s.CompoundType.setParseAction(lambda st, loc, toks: s.onCompoundType(s.CompoundType, st, loc, toks))
    s.Type << (s.TypeAtom | s.MapType | s.CompoundType) #pylint: disable=expression-not-assigned
    s.Type.setParseAction(lambda st, loc, toks: s.onType(s.Type, st, loc, toks))
    s.IdsType = G(csl(s.Id)) + S(s.COLN) + s.Type
    s.IdsType.setParseAction(lambda st, loc, toks: s.onBinding(s.Type, st, loc, toks))

    ####### Type Declarations
    s.TypeConstructor = S(s.TYPE) + G(s.AttrList) + G(O(s.FINITE)) + s.Id + G(ZoM(s.Id)) + S(s.SEMI)
    s.TypeConstructor.setParseAction(
            lambda st, loc, toks:  s.onTypeConstructorDecl(s.TypeConstructor, st, loc, toks))
    s.TypeSynonym = s.TYPE + s.AttrList + OoM(s.Id) + s.EQ + s.Type + s.SEMI
    s.TypeDecl = s.TypeConstructor | s.TypeSynonym

    ####### Constant Declarations
    s.ConstantDecl = S(s.CONST) + G(O(s.Attribute)) + G(O(s.UNIQUE)) + \
            s.IdsType + G(s.OrderSpec) + s.SEMI
    s.ConstantDecl.setParseAction(
            lambda st, loc, toks:  s.onConstDecl(s.ConstantDecl, st, loc, toks))


    s.Number = W(nums) # type: ParserElement[T]
    s.Number.setParseAction(
            lambda st, loc, toks:  s.onAtom(s.Number, st, loc, toks))
    s.BitVector = R("[0-9][0-9]*bv[0-9][0-9]*") # type: ParserElement[T]
    s.BitVector.setParseAction(
            lambda st, loc, toks:  s.onAtom(s.BitVector, st, loc, toks))
    # TODO
    # TrigAttr = Trigger | Attribute
    s.Old = s.OLD + s.LPARN + s.Expr + s.RPARN # type: ParserElement[T]
    s.Old.setParseAction(
            lambda st, loc, toks:  s.onAtom(s.Old, st, loc, toks))
    s.Primitive = s.FALSE | s.TRUE | s.Number | s.BitVector # type: ParserElement[T]
    # TODO: Handle TriggerAttrs in Quantified expressions
    #E9_Quantified = LPARN + QOp + O(TypeArgs) + csl(IdsType) \
    #        + QSep + ZoM(TrigAttr) + Expr  +  RPARN
    s.Quantified = S(s.LPARN) + s.QOp + O(s.TypeArgs) + \
            G(csl(s.IdsType)) + S(s.QSep) + s.Expr + S(s.RPARN)
    s.Quantified.setParseAction(
            lambda st, loc, toks:  s.onQuantified(s.Old, st, loc, toks))

    s.AtomIdCont = F()
    s.AtomId = s.Id + O(s.AtomIdCont)
    s.AtomId.setParseAction(
            lambda st, loc, toks:  s.onAtom(s.Id, st, loc, toks))
    s.Atom = (s.Primitive | s.Old | s.AtomId) # type: ParserElement[T]
    s.MapUpdateArgs = S(s.LSQBR) + s.Expr + s.ASSGN + s.Expr + S(s.RSQBR)
    s.MapUpdateArgs.setParseAction(
            lambda st, loc, toks:  s.onMapUpdateArgs(s.Old, st, loc, toks))
    s.MapIndexArgs = S(s.LSQBR) + s.Expr + S(s.RSQBR)
    s.MapIndexArgs.setParseAction(
            lambda st, loc, toks:  s.onMapIndexArgs(s.Old, st, loc, toks))
    s.FunAppArgs = s.LPARN + csl(s.Expr) + s.RPARN  # type: ParserElement[T]
    s.FunAppArgs.setParseAction(
            lambda st, loc, toks:  s.onFunAppArgs(s.FunAppArgs, st, loc, toks))
    s.AtomIdCont << (s.MapUpdateArgs | s.MapIndexArgs | s.FunAppArgs) + O(s.AtomIdCont)

    s.ArithExpr = operatorPrecedence(s.Atom, [
      (s.ArithUnOp, 1, opAssoc.RIGHT, \
           lambda st, loc, toks:  s.onUnaryOp(s.ArithUnOp, st, loc, toks[0])),
      (s.MulOp, 2, opAssoc.LEFT, \
           lambda st, loc, toks: s.onLABinOp(s.MulOp, st, loc, toks[0])),
      (s.AddOp, 2, opAssoc.LEFT, \
           lambda st, loc, toks: s.onLABinOp(s.AddOp, st, loc, toks[0])),
    ]) # type: ParserElement[T]
    # TODO: Add support for M[x,y,z:=foo], M[a:b], concat ops
    s.RelExpr = s.ArithExpr + s.RelOp + s.ArithExpr # type: ParserElement[T]
    s.RelExpr.setParseAction(
            lambda st, loc, toks: s.onNABinOp(s.RelExpr, st, loc, toks))

    s.BoolExpr = operatorPrecedence((s.RelExpr | s.Atom | s.Quantified), [
      (s.BoolUnOp, 1, opAssoc.RIGHT, \
              lambda st, loc, toks:  s.onUnaryOp(s.BoolUnOp, st, loc, toks[0])),
      (s.AndOrOp, 2, opAssoc.LEFT, \
              lambda st, loc, toks:  s.onLABinOp(s.AndOrOp, st, loc, toks[0])),
      (s.ImplOp, 2, opAssoc.LEFT, \
              lambda st, loc, toks:  s.onLABinOp(s.ImplOp, st, loc, toks[0])),
      (s.EquivOp, 2, opAssoc.LEFT, \
              lambda st, loc, toks:  s.onLABinOp(s.EquivOp, st, loc, toks[0])),
    ]) # type: ParserElement[T]

    s.Expr << (s.BoolExpr ^ s.RelExpr ^ s.ArithExpr ) #pylint: disable=pointless-statement

    ####### Function Declarations
    s.FArgName = s.Id + s.COLN
    s.FArg = s.FArgName + s.Type
    s.FSig = O(s.TypeArgs) + s.LPARN + csl(s.FArg) + \
            s.RPARN + s.RETURNS + s.LPARN + s.FArg + s.RPARN
    s.FunctionDecl = s.FUNCTION + s.AttrList + s.Id + s.FSig + s.SEMI |\
                     s.FUNCTION + s.AttrList + s.Id + s.FSig + s.SEMI +\
                        s.LBRAC + s.Expr + s.RBRAC

    ####### Axiom Declarations
    s.AxiomDecl = s.AXIOM + s.AttrList + s.Expr + s.SEMI
    s.AxiomDecl.setParseAction(
            lambda st, loc, toks: s.onAxiomDecl(s.RelExpr, st, loc, toks))

    s.WhereClause = F() # TODO

    s.IdsTypeWhere = s.IdsType + O(s.WhereClause)
    s.VarDecl = S(s.VAR) + G(s.AttrList) + s.IdsTypeWhere + s.SEMI
    s.VarDecl.setParseAction(
            lambda st, loc, toks: s.onVarDecl(s.RelExpr, st, loc, toks))

    ####### Procedure Declarations
    s.Spec =  G(G(O(s.FREE)) + s.REQUIRES + s.Expr + s.SEMI) \
          | G(G(O(s.FREE)) + s.MODIFIES + G(csl(s.Id)) + s.SEMI) \
          | G(G(O(s.FREE)) + s.ENSURES + s.Expr + s.SEMI)

    s.OutParameters = s.RETURNS + s.LPARN + csl(s.IdsTypeWhere) + s.RPARN
    s.PSig = G(O(s.TypeArgs)) + S(s.LPARN) + G(O(csl(s.IdsTypeWhere))) + \
            S(s.RPARN) + G(O(s.OutParameters))


    s.LocalVarDecl = S(s.VAR) + s.AttrList + csl(s.IdsTypeWhere) + \
            S(s.SEMI) # type: ParserElement[T]
    s.LocalVarDecl.setParseAction(
            lambda st, loc, toks: s.onLocalVarDecl(s.LocalVarDecl,
                                                   st, loc, toks))

    s.StmtList = F()
    s.WildcardExpr = s.Expr | s.STAR

    s.BlockStmt = s.LBRAC + s.StmtList + s.RBRAC

    s.LoopInv = O(s.FREE) + s.INVARIANT + s.Expr + s.SEMI

    s.IfStmt = F() # type: Union[F, ParserElement[T]]
    s.Else = s.ELSE + s.BlockStmt | s.ELSE + s.IfStmt
    s.IfStmt << s.IF + s.LBRAC + s.WildcardExpr + s.RBRAC + s.BlockStmt + \
            O(s.Else)

    s.CallLhs = csl(s.Id) + s.ASSGN
    s.Lhs =  s.Id + ZoM(s.MapIndexArgs)
    s.Lhs.setParseAction(
        lambda st, loc, toks: s.onAtom(s.Id, st, loc, toks))
    s.Label = s.Id | s.Number

    s.AssertStmt = S(s.ASSERT) + s.Expr + S(s.SEMI) # type: ParserElement[T]
    s.AssertStmt.setParseAction(
            lambda st, loc, toks: s.onAssert(s.AssertStmt, st, loc, toks))
    s.AssumeStmt = S(s.ASSUME) + G(s.AttrList) + s.Expr + S(s.SEMI) # type: ParserElement[T]
    s.AssumeStmt.setParseAction(
            lambda st, loc, toks: s.onAssume(s.AssumeStmt, st, loc, toks))
    s.ReturnStmt = S(s.RETURN) + S(s.SEMI) # type: ParserElement[T]
    s.ReturnStmt.setParseAction(
            lambda st, loc, toks: s.onReturn(s.ReturnStmt, st, loc, toks))
    s.GotoStmt = S(s.GOTO) + csl(s.Label) + S(s.SEMI) # type: ParserElement[T]
    s.GotoStmt.setParseAction(
            lambda st, loc, toks: s.onGoto(s.GotoStmt, st, loc, toks))
    s.AssignmentStmt = G(csl(s.Lhs)) + S(s.ASSGN) + G(csl(s.Expr)) + S(s.SEMI) # type: ParserElement[T]
    s.AssignmentStmt.setParseAction(
            lambda st, loc, toks: s.onAssignment(s.AssignmentStmt, st,
                                                 loc, toks))
    s.HavocStmt = S(s.HAVOC) + csl(s.Id) + S(s.SEMI) # type: ParserElement[T]
    s.HavocStmt.setParseAction(
            lambda st, loc, toks: s.onHavoc(s.HavocStmt, st, loc, toks))

    s.CallAssignStmt = S(s.CALL) + G(O(s.AttrList)) + G(O(s.CallLhs)) + s.Id +\
            S(s.LPARN) + G(O(csl(s.Expr))) + S(s.RPARN) + S(s.SEMI)
    s.CallAssignStmt.setParseAction(
            lambda st, loc, toks: s.onCallAssignStmt(s.CallAssignStmt, st, loc, toks))
    s.CallForallStmt = s.CALL + s.FORALL + s.Id + s.LPARN + \
            csl(s.WildcardExpr) + s.RPARN + S(s.SEMI)

    s.WhileStmt = s.WHILE + s.LPARN + s.WildcardExpr + s.RPARN + \
            ZoM(s.LoopInv) + s.BlockStmt
    s.BreakStmt = s.BREAK + O(s.Id) + S(s.SEMI)

    s.Stmt = s.AssertStmt \
          | s.AssumeStmt \
          | s.HavocStmt \
          | s.AssignmentStmt \
          | s.CallAssignStmt \
          | s.CallForallStmt \
          | s.IfStmt \
          | s.WhileStmt \
          | s.BreakStmt \
          | s.ReturnStmt \
          | s.GotoStmt # type: ParserElement[T]

    s.LStmt = F()
    s.LabeledStatement = s.Label + S(s.COLN) + s.LStmt # type: ParserElement[T]
    s.LEmpty = (s.Label + S(s.COLN) ) 
    s.LStmt << (s.Stmt | s.LabeledStatement | s.LEmpty) #pylint: disable=pointless-statement
    s.LabeledStatement.setParseAction(
      lambda st, loc, toks: s.onLabeledStatement(s.LabeledStatement,
                                                 st, loc, toks))
    s.LEmpty.setParseAction(
      lambda st, loc, toks: s.onLabeledStatement(s.LEmpty,
                                                 st, loc, toks))

    s.StmtList << (ZoM(s.LStmt)) #pylint: disable=expression-not-assigned


    s.Body = S(s.LBRAC) + G(ZoM(s.LocalVarDecl)) + G(s.StmtList) + S(s.RBRAC) # type: ParserElement[T]
    s.Body.setParseAction(lambda st, loc, toks: s.onBody(s.Body, st, loc, toks))

    s.ProcedureDecl = \
        S(s.PROCEDURE) + G(s.AttrList) + s.Id + G(s.PSig) + S(s.SEMI) + G(ZoM(s.Spec)) |\
        S(s.PROCEDURE) + G(s.AttrList) + s.Id + G(s.PSig) + G(ZoM(s.Spec)) + s.Body
    s.ProcedureDecl.setParseAction(
      lambda st, loc, toks: s.onProcedureDecl(s.ProcedureDecl, st, loc, toks))

    s.IOutParameters = S(s.RETURNS) + S(s.LPARN) + csl(s.IdsType) + S(s.RPARN)
    s.ISig = G(O(s.TypeArgs)) + S(s.LPARN) + G(O(csl(s.IdsType))) + S(s.RPARN) +\
            G(O(s.IOutParameters))
    s.ImplementationDecl = S(s.IMPLEMENTATION) + G(s.AttrList) + s.Id +\
            G(s.ISig) + G(ZoM(s.Body)) # type: ParserElement[T]
    s.ImplementationDecl.setParseAction(
      lambda st, loc, toks: s.onImplementationDecl(s.ImplementationDecl,
                                                   st, loc, toks))


    s.Decl : ParserElement[T] = s.TypeDecl |\
             s.ConstantDecl |\
             s.FunctionDecl |\
             s.AxiomDecl |\
             s.VarDecl |\
             s.ProcedureDecl |\
             s.ImplementationDecl

    s.Program = ZoM(s.Decl) # type: ParserElement[T]
    s.Program.setParseAction(
            lambda st, loc, toks: s.onProgram(s.Program, st, loc, toks))
    s.Program.ignore(L("//") + restOfLine)

  def parseExpr(s, st:str) -> T:
    return (s.Expr + StringEnd()).parseString(st)[0]

  def parseStmt(s, st:str) -> T:
    return (s.LStmt + StringEnd()).parseString(st)[0]

  def parseProgram(s, st:str) -> T:
    return (s.Program + StringEnd()).parseString(st)[0]

  def parseBinding(s, st:str) -> Iterable[T]:
    return (s.IdsType + StringEnd()).parseString(st)

  def parseType(s, st:str) -> T:
    return (s.Type + StringEnd()).parseString(st)[0]
