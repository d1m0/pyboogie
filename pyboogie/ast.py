#pylint: disable=no-self-argument,multiple-statements
from .grammar import BoogieParser
from .util import ccast, clcast, ite
from pyparsing import ParseResults as PR, ParserElement as PE
from functools import reduce
from typing import List, Iterable, Set, TYPE_CHECKING, Any, Union, Dict, \
        TypeVar, Callable, Tuple, NamedTuple, Type, Optional
from attr import attrs, attrib
from re import compile

LabelT = str
T = TypeVar("T")

class AstNode:
    def __eq__(self, other: object) -> bool:
        """ Ast nodes compare via structural equality """
        if other.__class__ != self.__class__:
            return False
        return self.__dict__ == other.__dict__

# Types
class AstType(AstNode): pass
# Builtin Types
class AstBuiltinType(AstType): pass
@attrs(frozen=True)
class AstIntType(AstBuiltinType):
    def __str__(s) -> str: return "int"
@attrs(frozen=True)
class AstBoolType(AstBuiltinType):
    def __str__(s) -> str: return "bool"
@attrs(frozen=True)
class AstBVType(AstBuiltinType):
    numBits = attrib(type=int)
    def __str__(s) -> str: return "int"
@attrs(frozen=True)
class AstMapType(AstBuiltinType):
    typeVars = attrib(type=List[str])
    domainT = attrib(type=List[AstType])
    rangeT = attrib(type=AstType)
    def __str__(s) -> str: return "{}[{}]{}".format(
        ("" if len(s.typeVars) == 0 else "<{}>".format(",".join(s.typeVars))),
        ",".join(map(str, s.domainT)),
        str(s.rangeT))

# User-defined type constructors
@attrs(frozen=True)
class AstCompoundType(AstType):
    name = attrib(type=str)
    typeArgs = attrib(type=List[AstType])
    def __str__(s) -> str: return "{} {}".format(s.name, " ".join(map(str, s.typeArgs)))

# Expressions
class AstExpr(AstNode): pass
@attrs(frozen=True)
class AstFalse(AstExpr):
    def __str__(s) -> str: return "false"

@attrs(frozen=True)
class AstTrue(AstExpr):
    def __str__(s) -> str: return "true"

@attrs(frozen=True)
class AstNumber(AstExpr):
    num = attrib(type=int)
    def __str__(s) -> str: return str(s.num)

@attrs(frozen=True)
class AstId(AstExpr):
    name = attrib(type=str)
    def __str__(s) -> str: return s.name

@attrs(frozen=True)
class AstWildcard(AstExpr):
    def __str__(s) -> str: return "*"

@attrs(frozen=True)
class AstMapIndex(AstExpr):
    map = attrib(type=AstExpr)
    index = attrib(type=AstExpr)
    def __str__(s) -> str: return "{}[{}]".format(str(s.map), str(s.index))

@attrs(frozen=True)
class AstMapUpdate(AstExpr):
    map = attrib(type=AstExpr)
    index = attrib(type=AstExpr)
    newVal = attrib(type=AstExpr)
    def __str__(s) -> str: return "{}[{}:={}]".format(str(s.map), str(s.index), str(s.newVal))

class AstInternalExpr(AstExpr):
    """ Ast Expression nodes used only during parsing. """

@attrs(frozen=True)
class AstMapUpdateArgs(AstInternalExpr):
    index = attrib(type=AstExpr)
    newVal = attrib(type=AstExpr)
    def __str__(s) -> str: return "[{}:={}]".format(str(s.index), str(s.newVal))

@attrs(frozen=True)
class AstMapIndexArgs(AstInternalExpr):
    index = attrib(type=AstExpr)
    def __str__(s) -> str: return "[{}]".format(str(s.index))

@attrs(frozen=True)
class AstFuncExprArgs(AstInternalExpr):
    args = attrib(type=List[AstExpr])
    def __str__(s) -> str: return "({})".format(",".join(map(str, s.args)))

@attrs(frozen=True)
class AstUnExpr(AstExpr):
    op = attrib(type=str)
    expr = attrib(type=AstExpr)
    def __str__(s) -> str: return s.op + str(s.expr)

@attrs(frozen=True)
class AstBinExpr(AstExpr):
    lhs = attrib(type=AstExpr)
    op = attrib(type=str)
    rhs = attrib(type=AstExpr)
    def __str__(s) -> str:
        return "(" + str(s.lhs) + " " + str(s.op) + " " + str(s.rhs) + ")"

@attrs(frozen=True)
class AstTernary(AstExpr):
    condition = attrib(type=AstExpr)
    thenE = attrib(type=AstExpr)
    elseE = attrib(type=AstExpr)
    def __str__(s) -> str:
        return "if (" + str(s.condition) + ") then " + str(s.thenE) + " else " + str(s.elseE)

@attrs(frozen=True)
class AstAttribute(AstNode):
    name = attrib(type=str)
    args = attrib(type=List[Union[str, AstExpr]])
    def __str__(s) -> str:
        return "{ :" + s.name + " " + ",".join(map(str, s.args)) + "}"

@attrs(frozen=True)
class AstBinding(AstNode):
    names = attrib(type=Tuple[str,...])
    typ = attrib(type=AstType)
    def __str__(s) -> str: return ",".join(map(str, s.names)) + " : " + str(s.typ)


@attrs(frozen=True)
class AstForallExpr(AstExpr):
    bindings = attrib(type=Tuple[AstBinding,...])
    expr = attrib(type=AstExpr)
    def __str__(s) -> str:
        return "(forall " + ",".join(map(str, s.bindings)) + " :: " + \
               str(s.expr) + ")"

@attrs(frozen=True)
class AstFuncExpr(AstExpr):
    funcName = attrib(type=str)
    ops = attrib(type=List[AstExpr])
    def __str__(s) -> str:
        return str(s.funcName) + "(" + ",".join(map(str, s.ops)) +  ")"

def stripOutsideParenthesis(e: AstExpr) -> str:
    s = str(e)
    if isinstance(e, AstForallExpr) or isinstance(e, AstBinExpr):
        stripRe = compile("^ *\((.*)\) *$")
        m = stripRe.match(s)
        assert m is not None, "{} doesn't match RE {}".format(s, stripRe)
        s = m.groups()[0]
    return s

class AstStmt(AstNode): pass

@attrs(frozen=True)
class AstLabel(AstStmt):
    label = attrib(type=str)
    stmt = attrib(type=AstStmt)
    def __str__(s) -> str: return str(s.label) + " : " + str(s.stmt)

@attrs(frozen=True)
class AstOneExprStmt(AstStmt):
    expr = attrib(type=AstExpr)

class AstAssert(AstOneExprStmt):
    def __str__(s) -> str: return "assert " + stripOutsideParenthesis(s.expr) + ";"

class AstAssume(AstOneExprStmt):
    def __str__(s) -> str: return "assume " + stripOutsideParenthesis(s.expr) + ";"

@attrs(frozen=True)
class AstAssignment(AstStmt):
    lhs = attrib(type=List[Union[AstId, AstMapIndex]])
    rhs = attrib(type=List[AstExpr])
    def __str__(s) -> str:
        return ",".join(map(str, s.lhs)) + " := " + ",".join(map(stripOutsideParenthesis, s.rhs)) + ";"

@attrs(frozen=True)
class AstHavoc(AstStmt):
    ids = attrib(type=List[AstId])
    def __str__(s) -> str: return "havoc " + ",".join(map(str, s.ids)) + ";"

# Returns is for now without argument
class AstReturn(AstStmt):
    def __str__(s) -> str: return "return ;"

@attrs(frozen=True)
class AstGoto(AstStmt):
    labels = attrib(type=List[LabelT])
    def __str__(s) -> str: return "goto " + ",".join(map(str, s.labels)) + ";"


@attrs(frozen=True)
class AstCall(AstStmt):
    attributes = attrib(type=List[AstAttribute])
    lhs = attrib(type=Optional[List[AstId]])
    id = attrib(type=str)
    arguments = attrib(type=List[AstExpr])

    def __str__(s) -> str:
        res = "call "
        if s.lhs is not None:
            res += ",".join(map(str, s.lhs)) + ":="
        res += s.id + "(" + ",".join(map(str, s.arguments)) + ");"
        return res

# Non-Simple Statements
@attrs(frozen=True)
class AstIf(AstStmt):
    condition = attrib(type=AstExpr)
    thenS = attrib(type=List[AstStmt])
    elseS = attrib(type=Optional[Union[List[AstStmt], AstStmt]])

    def __str__(s) -> str:
        res = "if (" + str(s.condition) + ") {\n"
        res += "\n".join(map(str, s.thenS)) + '\n}'
        if s.elseS is None:
            return res

        if isinstance(s.elseS, AstStmt):
            res += ' else ' + str(s.elseS)
        else:
            res += ' else {\n' + '\n'.join(map(str, s.elseS)) + '\n}'
        return res

# Functions
@attrs(frozen=True)
class AstBody(AstNode):
    bindings = attrib(type = List[AstBinding])
    stmts = attrib(type = List[AstStmt])
    def __str__(s) -> str:
        return "{\n" + "\n".join(["var " + str(x) + ";" for x in s.bindings]) +\
                "\n" +\
                "\n".join([str(x) for x in s.stmts]) + \
                "\n}"

# Declarations
class AstDecl(AstNode): pass

@attrs(frozen=True)
class AstVarDecl(AstDecl):
    attributes = attrib(type=List[AstAttribute])
    binding = attrib(type=AstBinding)

    def __str__(s) -> str:
        return "var " + " ".join(map(str, s.attributes)) + str(s.binding) + ";"


@attrs(frozen=True)
class AstFunctionDecl(AstDecl):
    attributes = attrib(type=List[AstAttribute])
    id = attrib(type=str)
    parameters = attrib(type=List[AstBinding])
    returns = attrib(type=AstType)
    body = attrib(type=Optional[AstExpr])

    def __str__(s) -> str:
        res = "function "
        res += " ".join(map(str, s.attributes)) + " "
        res += s.id
        res += "(" + ",".join(map(str, s.parameters)) + ")"
        res += "returns (" + str(s.returns) + ")"
        if (s.body is not None):
            res += "{" + str(s.body) + "}"
        else:
            res += ";"
        return res


@attrs(frozen=True)
class AstAxiomDecl(AstDecl):
    attributes = attrib(type=List[AstAttribute])
    expr = attrib(type=AstExpr)

    def __str__(s) -> str:
        return "axiom " + " ".join(map(str, s.attributes)) + str(s.expr) + ";"


@attrs(frozen=True)
class AstConstDecl(AstDecl):
    attributes = attrib(type=List[AstAttribute])
    unique = attrib(type=bool)
    binding = attrib(type=AstBinding)

    def __str__(s) -> str:
        return "const " + " ".join(map(str, s.attributes)) + \
                ite(s.unique, " unique ", "") + str(s.binding) + ";"


@attrs(frozen=True)
class AstImplementation(AstDecl):
    name = attrib(type = str)
    parameters = attrib(type = List[AstBinding])
    returns = attrib(type = List[AstBinding])
    body = attrib(type = AstBody)
    def __str__(s) -> str:
        return "implementation " + s.name + " (" +\
            ",".join(map(str,s.parameters)) + ") " +\
            ("returns (" + ",".join(map(str,s.returns)) + ")" if (len(s.returns) != 0) else "") +\
            str(s.body)

@attrs(frozen=True)
class AstProcedure(AstDecl):
    attributes = attrib(type=List[AstAttribute])
    name = attrib(type=str)
    parameters = attrib(type=List[AstBinding])
    returns = attrib(type=List[AstBinding])
    requires = attrib(type=List[Tuple[bool, AstExpr]])
    ensures = attrib(type=List[Tuple[bool, AstExpr]])
    modifies = attrib(type=List[Tuple[bool, str]])
    body = attrib(type=Optional[AstBody])

    def __str__(s) -> str:
        spec = ""

        for (free, expr) in s.requires:
            spec += "\n " + ite(free, "free ", "") + "requires " + str(expr) + ";"
        for (free, id) in s.modifies:
            spec += "\n " + ite(free, "free ", "") + "modifies " + str(id) + ";"
        for (free, expr) in s.ensures:
            spec += "\n " + ite(free, "free ", "") + "modifies " + str(expr) + ";"

        res = "procedure " + " ".join(map(str, s.attributes)) + s.name
        res += "(" + ",".join(map(str, s.parameters)) + ")"
        res += "returns (" + ",".join(map(str, s.returns)) + ")"

        if (s.body is None):
            res += ";" + spec
        else:
            res += spec + "\n" + str(s.body)

        return res

@attrs(frozen=True)
class AstTypeConstructorDecl(AstDecl):
    name = attrib(type=str)
    formals = attrib(type=List[str])
    isFinite = attrib(type=bool)
    attributes = attrib(type=List[AstAttribute])
    def __str__(s) -> str:
        return "type " + " ".join(map(str, s.attributes)) +\
            (" finite" if s.isFinite else " ") +\
            s.name + " " + " ".join(s.formals) + ";"

# Programs
@attrs(frozen=True)
class AstProgram(AstNode):
    decls = attrib(type=List[AstDecl])
    def __str__(s) -> str: return "\n".join(map(str, s.decls))

def _mkBinExp(lhs: Any, op: Any, rhs: Any) -> AstBinExpr:
  assert isinstance(lhs, AstExpr) and isinstance(rhs, AstExpr) and \
         isinstance(op, str)
  return AstBinExpr(lhs, op, rhs)

def listify(p: "PR[T]") -> "List[T]":
    if (len(p) == 0):
        return [] 
    return [x for x in p]

ReplMap_T = Dict[AstNode, AstNode]
def replace(ast: Any, m: ReplMap_T) -> AstNode:
    if (not isinstance(ast, AstNode)):
        return ast
    else:
        if (ast in m):
            return m[ast]
        else:
            return ast.__class__(*[replace(val,m) for (field, val) in ast.__dict__.items()])

def reduce_nodes(node: AstNode, cb: Callable[[AstNode, List[T]], T]) -> T:
    return cb(node,
              [ reduce_nodes(val, cb)
                  for val in node.__dict__.values() if isinstance(val, AstNode) ])

class AstBuilder(BoogieParser[AstNode]):
  def onAtom(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    if prod == s.TRUE:
      assert len(toks) == 1
      return [ AstTrue() ]
    elif prod == s.FALSE:
      assert len(toks) == 1
      return [ AstFalse() ]
    elif prod == s.Number:
      assert len(toks) == 1
      return [ AstNumber(int(toks[0])) ]
    else:
      res = AstId(str(toks[0])) # type: AstExpr
      for cont in toks[1:]:
        if (isinstance(cont, AstMapIndexArgs)):
            res = AstMapIndex(res, cont.index)
        elif (isinstance(cont, AstMapUpdateArgs)):
            res = AstMapUpdate(res, cont.index, cont.newVal)
        elif (isinstance(cont, AstFuncExprArgs)):
            assert (isinstance(res, AstId))
            res = AstFuncExpr(res.name, cont.args)
        else:
            assert False, "Unexpected token after id: " + str(cont)

      return [res]

  def onUnaryOp(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    op = str(toks[0])
    expr = toks[1]
    assert isinstance(expr, AstExpr)
    return [ AstUnExpr(op, expr) ]

  def onLABinOp(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    if (len(toks) == 3):
      return [ _mkBinExp(*toks) ]
    else:
      assert(len(toks) > 3)
      base = _mkBinExp(*toks[:3])
      rest = [ [toks[3+2*k], toks[3+2*k+1]] for k in range(int((len(toks)-3)/2)) ]
      return [ reduce(lambda acc,el:  _mkBinExp(acc, el[0], el[1]), \
                      rest, base)
             ]

  def onRABinOp(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    raise Exception("NYI")

  def onNABinOp(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 3)
    return [ _mkBinExp(*toks) ]

  def onBinding(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    ids = map(str, toks[0])
    typ = toks[1]
    return [AstBinding(tuple(ids), typ)]

  def onTypeConstructorDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    return [ AstTypeConstructorDecl(
                ccast(toks[2], AstId).name,
                [x.name for x in clcast(toks[3], AstId)],
                (len(toks[1]) != 0),
                clcast(toks[0], AstAttribute))]

  def onAttribute(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    args : List[Union[str, AstExpr]] = []
    for x in toks[1]:
        assert (isinstance(x, str) or isinstance(x, AstExpr))
        args.append(x)
    return [ AstAttribute(ccast(toks[0], AstId).name, args) ]

  # Statements
  def onAssert(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 1 and isinstance(toks[0], AstExpr))
    return [ AstAssert(toks[0]) ]
  def onAssume(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 2)
    # TODO: Don't ignore attribute list
    return [ AstAssume(ccast(toks[1], AstExpr)) ]
  def onReturn(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 0)
    return [ AstReturn() ]
  def onGoto(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert(len(toks) > 0)
    return [ AstGoto([x.name for x in clcast(toks, AstId)]) ]
  def onAssignment(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    return [ AstAssignment(listify(toks[0]), listify(toks[1])) ]
  def onHavoc(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) > 0)
    return [ AstHavoc(clcast(toks, AstId)) ]

  def onCallAssignStmt(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    attributes = toks[0]
    lhs = toks[1]
    id = toks[2]
    arguments = toks[3]
    return [AstCall(attributes, lhs, id.name, arguments)]

  def onIfStmt(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    elseNode: Optional[Union[List[AstStmt], AstStmt]] = None
    if len(toks) == 3:
        if isinstance(toks[2], AstStmt):
            elseNode = ccast(toks[2], AstIf)
        else:
            elseNode = clcast(toks[2], AstStmt)

    return [AstIf(ccast(toks[0], AstExpr),
                  clcast(toks[1], AstStmt),
                  elseNode)]

  def onProgram(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    decls = [ccast(x, AstDecl) for x in toks] # type: List[AstDecl] 
    return [ AstProgram(decls) ]
  def onLocalVarDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 1 and isinstance(toks[0], AstBinding)
    return toks
  def onPrimitiveType(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    # Currently only handle ints
    assert len(toks) == 1
    if prod == s.INT:
      return [ AstIntType() ]
    elif prod == s.BOOL:
      return [ AstBoolType() ]
    else:
      assert prod == s.BVType
      assert toks[0][0:2] == 'bv'
      return [ AstBVType(int(toks[0][2:])) ]
  def onMapType(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 3
    return [ AstMapType([x.name for x in clcast(toks[0], AstId)], clcast(toks[1], AstType), ccast(toks[2], AstType)) ]
  def onCompoundType(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    args = [] # type: List[AstType]
    for t in toks[1:]:
        if isinstance(t, AstId):
            args.append(AstCompoundType(t.name, []))
        else:
            assert isinstance(t, AstType)
            args.append(t)
    return [ AstCompoundType(ccast(toks[0], AstId).name, args) ]

  def onType(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 1
    return [ ccast(toks[0], AstType) ]
  def onBody(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 2
    return [AstBody(clcast(toks[0], AstBinding), clcast(toks[1], AstStmt))]

  def onVarDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    attributes = toks[0]
    binding = toks[1]
    return [AstVarDecl(attributes, binding)]

  def onAxiomDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    attributes = toks[0]
    expr = toks[1]
    return [AstAxiomDecl(attributes, expr)]

  def onFunctionDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    attributes = toks[0]
    id = toks[1].name
    (type_args, parameters, returns) = toks[2]
    assert len(type_args) == 0
    body = toks[3] if len(toks) == 4 else None
    return [AstFunctionDecl(listify(attributes), id, listify(parameters), returns, body)]

  def onConstDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    attributes = toks[0]
    unique = len(toks[1]) != 0
    binding = toks[2]
    orderSpec = toks[3]
    assert len(orderSpec) == 0, "Order spec {} NYI".format(orderSpec)
    res =[AstConstDecl(attributes, unique, binding)]
    return res

  def onImplementationDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    attrs = toks[0]
    assert(len(attrs) == 0)
    name = str(toks[1])
    signature = toks[2]
    assert len(signature) == 3
    (type_args, parameters, returns) = signature # type: Tuple[PR[Any], PR[AstBinding], PR[AstBinding]]
    # For now ignore anything other than the argument list
    assert len(type_args) == 0, "NYI: Imeplementation type args: {}".format(type_args)
    body = toks[3][0]  # type: AstBody
    return [ AstImplementation(name, listify(parameters), listify(returns), body) ]


  def onProcedureDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    attributes = toks[0]
    name = str(toks[1])
    signature = toks[2]
    assert len(signature) == 3
    (type_args, parameters, returns) = signature # type: Tuple[PR[Any], PR[AstBinding], PR[AstBinding]]
    # For now ignore anything other than the argument list
    assert len(type_args) == 0, "NYI: Imeplementation type args: {}".format(type_args)
    spec = toks[3]
    body = toks[4] if (len(toks) ==5) else None  # type: Optional[AstBody]
    requires: List[Tuple[bool, AstExpr]] = []
    ensures: List[Tuple[bool, AstExpr]] = []
    modifies: List[Tuple[bool, str]] = []

    for (free, typ, arg) in spec:
        isFree = len(free) != 0
        if typ == "requires":
          requires.append((isFree, arg))
        elif typ == "modifies":
          modifies.extend([(isFree, id.name) for id in arg])
        elif typ == "ensures":
          ensures.append((isFree, arg))
        else:
            assert False, "Unknown spec type " + typ

    return [
        AstProcedure(attributes, name,
                     listify(parameters), listify(returns),
                     requires, ensures, modifies, body)]

  def onLabeledStatement(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    label = str(toks[0]) # type: LabelT
    if (len(toks) == 1):
        # Empty label
        return [AstLabel(label, None)]  #type: ignore
    else:
        stmt = toks[1]
        assert isinstance(stmt, AstStmt) or isinstance(stmt, AstLabel), "Unexpected {}".format(stmt)
        return [AstLabel(label, stmt)]  #type: ignore
  def onMapIndexArgs(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 1)
    return [AstMapIndexArgs(ccast(toks[0], AstExpr))]
  def onMapUpdateArgs(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 2)
    return [AstMapUpdateArgs(ccast(toks[0], AstExpr), ccast(toks[1], AstExpr))]
  def onFunAppArgs(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    return [AstFuncExprArgs([ccast(x, AstExpr) for x in toks])]
  def onQuantified(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 3, "NYI TypeArgs on quantified expressions"
    quantifier = str(toks[0])
    bindings = []  # type: List[AstBinding]
    for node in toks[1]:
        assert isinstance(node, AstBinding)
        bindings.append(node)
    expr = toks[2]
    assert quantifier == "forall", "Existential quantification NYI"
    return [AstForallExpr(tuple(bindings), ccast(expr, AstExpr))]
  def onWildcardExpr(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    if len(toks) == 1 and str(toks[0]) == "*":
        return [AstWildcard()]

    return toks
  def onTernary(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    return [AstTernary(ccast(toks[0], AstExpr),
                      ccast(toks[1], AstExpr),
                      ccast(toks[2], AstExpr))]

astBuilder = AstBuilder()

def parseExprAst(s: str) -> AstExpr:
  try:
    return ccast(astBuilder.parseExpr(s), AstExpr)
  except:
    print("Failed parsing")
    raise

def parseStmt(s: str) -> AstStmt:
  try:
    return ccast(astBuilder.parseStmt(s), AstStmt)
  except:
    print("Failed parsing")
    raise

def parseDecl(s: str) -> AstDecl:
  try:
    return ccast(astBuilder.parseDecl(s), AstDecl)
  except:
    print("Failed parsing {}".format(s))
    raise

def parseAst(s: str) -> AstProgram:
  try:
    return ccast(astBuilder.parseProgram(s), AstProgram)
  except:
    print("Failed parsing")
    raise

def parseBinding(s: str) -> Iterable[AstBinding]:
  try:
    return map(lambda x:    ccast(x, AstBinding), astBuilder.parseBinding(s))
  except:
    print("Failed parsing")
    raise

def parseType(s: str) -> AstType:
  try:
    return ccast(astBuilder.parseType(s), AstType)
  except:
    print("Failed parsing")
    raise

def expr_read(ast: AstNode) -> Set[str]:
    if isinstance(ast, AstId):
        return set([ast.name])
    elif isinstance(ast, AstNumber):
        return set()
    elif isinstance(ast, AstUnExpr):
        return expr_read(ast.expr)
    elif isinstance(ast, AstBinExpr):
        return expr_read(ast.lhs).union(expr_read(ast.rhs))
    elif isinstance(ast, AstTrue) or isinstance(ast, AstFalse):
        return set()
    elif isinstance(ast, AstForallExpr):
        quantified_ids = set(name for binding in ast.bindings for name in binding.names) # type: Set[str]
        return expr_read(ast.expr).difference(quantified_ids)
    elif isinstance(ast, AstMapIndex):
        return expr_read(ast.map).union(expr_read(ast.index))
    elif isinstance(ast, AstMapUpdate):
        return expr_read(ast.map).union(expr_read(ast.index)).union(expr_read(ast.newVal))
    else:
        raise Exception("Unknown expression type " + str(ast))

def stmt_read(ast: AstStmt) -> Set[str]:
    if isinstance(ast, AstLabel):
        ast = ast.stmt

    if isinstance(ast, AstAssume) or isinstance(ast, AstAssert):
        return expr_read(ast.expr)
    elif isinstance(ast, AstAssignment):
        # Map assignments should be re-written using MapUpdate syntax
        assert all(isinstance(x, AstId) for x in ast.lhs)
        return reduce(lambda acc, x: acc.union(expr_read(x)), ast.rhs, set())
    elif isinstance(ast, AstHavoc):
        return set()
    else:
        raise Exception("Unknown statement: " + str(ast))

def stmt_changed(ast: AstStmt) -> Set[str]:
    if isinstance(ast, AstLabel):
        ast = ast.stmt

    if isinstance(ast, AstAssignment):
        # Map assignments should be re-written using MapUpdate syntax
        assert all(isinstance(x, AstId) for x in ast.lhs), "Bad lhs: {}".format(ast.lhs)
        return set(map(str, ast.lhs))
    elif isinstance(ast, AstHavoc):
        return set([x.name for x in ast.ids])
    elif isinstance(ast, AstAssume) or isinstance(ast, AstAssert):
        return set([])
    else:
        raise Exception("Unknown statement: " + str(ast))

def ast_group_bin(exprs: List[AstExpr], op: str, default: AstExpr) -> AstExpr:
    if (len(exprs) == 0):
      return default
    if (len(exprs) == 1):
      return exprs[0]

    return reduce(lambda x,y:   AstBinExpr(x, op, y), exprs[1:], exprs[0])

def ast_and(exprs: Iterable[AstExpr]) -> AstExpr: return ast_group_bin(list(exprs), "&&", AstTrue())
def ast_or(exprs: Iterable[AstExpr]) -> AstExpr: return ast_group_bin(list(exprs), "||", AstFalse())

def normalize(ast: AstNode) -> AstNode:
  # There are 2 ways to encode "-1" - as an AstUnExpr or an AstNumber. We pick
  # the AstUnExpr to be the canonical one for compatibility with the grammar
  # TODO: What happens when we parse -0?
  if (isinstance(ast, AstNumber) and ast.num < 0):
    return AstUnExpr("-", AstNumber(abs(ast.num)))
  # There are 2 ways to encode implication - as a ==> b or (!a) || b. The later
  # usually comes from the frontend, since JS lacks an explicit ==> operator.
  # We pick a ==> b to be canonical

  if (isinstance(ast, AstBinExpr) and ast.op == "||" and \
      isinstance(ast.lhs, AstUnExpr) and ast.lhs.op == "!"):
    return AstBinExpr(ast.lhs.expr, "==>", ast.rhs)

  if (isinstance(ast, AstNode)):
    return ast.__class__(*tuple(map(normalize, ast.__dict__.values())))
  else:
    return ast

def ast_constants(n: AstNode) -> Set[int]:
  def cb(node: AstNode, children: Iterable[Set[int]]) -> Set[int]:
    if isinstance(node, AstNumber):
      return set([node.num])
    else:
      return reduce(lambda x,y: x.union(y), children, set())
  return reduce_nodes(n, cb)


def ast_boolean_exprs(n: AstNode) -> Set[AstExpr]:
  def cb(node: AstNode, children: Iterable[Set[AstExpr]]) -> Set[AstExpr]:
    relOps = [ "<", ">", "<=", ">=", "==",  "!=" ]
    boolOps = [ "||", "&&", "==>", "<==>" ]
    isBoolean = (isinstance(node, AstUnExpr) and node.op == "!") or \
                (isinstance(node, AstBinExpr) and node.op in (relOps + boolOps))
    base = set([]) # type: Set[AstExpr]
    boolSubexp = reduce(lambda x,y: x.union(y), children, base)
    if (isBoolean):
      assert isinstance(node, AstExpr)
      boolSubexp.add(node)
    return boolSubexp

  return reduce_nodes(n, cb)

def ast_primitive_boolean_exprs(n: AstNode) -> Set[AstExpr]:
  def cb(node: AstNode, children: Iterable[Set[AstExpr]]) -> Set[AstExpr]:
    relOps = [ "<", ">", "<=", ">=", "==",  "!=" ]
    isBoolean = (isinstance(node, AstBinExpr) and node.op in relOps)
    base = set([]) # type: Set[AstExpr]
    boolSubexp = reduce(lambda x,y: x.union(y), children, base)
    if (isBoolean):
      assert isinstance(node, AstExpr)
      boolSubexp.add(node)
    return boolSubexp

  return reduce_nodes(n, cb)
