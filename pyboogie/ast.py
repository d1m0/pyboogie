#pylint: disable=no-self-argument,multiple-statements
from .grammar import BoogieParser
from .util import ccast
from pyparsing import ParseResults as PR, ParserElement as PE
from functools import reduce
from typing import List, Iterable, Set, TYPE_CHECKING, Any, Union, Dict, TypeVar, Callable, Tuple, NamedTuple, Type

from attr import attrs, attrib
class AstNode:
    def __eq__(self, other: object) -> bool:
        """ Ast nodes compare via structural equality """
        if other.__class__ != self.__class__:
            return False
        return self.__dict__ == other.__dict__

# Types
class AstType(AstNode): pass
class AstIntType(AstType):
    def __str__(s) -> str: return "int"
class AstBoolType(AstType):
    def __str__(s) -> str: return "bool"

@attrs(frozen=True)
class AstMapType(AstType):
    domainT = attrib(type=AstType)
    rangeT = attrib(type=AstType)
    def __str__(s) -> str: return "[{}]{}".format(str(s.domainT), str(s.rangeT))

# Expressions
class AstExpr(AstNode): pass
class AstFalse(AstExpr):
    def __str__(s) -> str: return "false"

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
class AstBinding(AstNode):
    names = attrib(type=List[str])
    typ = attrib(type=AstType)
    def __str__(s) -> str: return ",".join(map(str, s.names)) + " : " + str(s.typ)


@attrs(frozen=True)
class AstForallExpr(AstExpr):
    bindings = attrib(type=List[AstBinding])
    expr = attrib(type=AstExpr)
    def __str__(s) -> str:
        return "(forall " + ",".join(map(str, s.bindings)) + " :: " + \
               str(s.expr) + ")"

@attrs(frozen=True)
class AstFuncExpr(AstExpr):
    funcName = attrib(type=AstId)
    ops = attrib(type=List[AstExpr])
    def __str__(s) -> str:
        return str(s.funcName) + "(" + ",".join(map(str, s.ops)) +  ")"

class AstStmt(AstNode): pass

@attrs(frozen=True)
class AstLabel(AstNode):
    label = attrib(type=str)
    stmt = attrib(type=AstStmt)
    def __str__(s) -> str: return str(s.label) + " : " + str(s.stmt)

@attrs(frozen=True)
class AstOneExprStmt(AstStmt):
    expr = attrib(type=AstExpr)

class AstAssert(AstOneExprStmt):
    def __str__(s) -> str: return "assert (" + str(s.expr) + ");"

class AstAssume(AstOneExprStmt):
    def __str__(s) -> str: return "assume (" + str(s.expr) + ");"

@attrs(frozen=True)
class AstAssignment(AstStmt):
    lhs = attrib(type=Union[AstId, AstMapIndex])
    rhs = attrib(type=AstExpr)
    def __str__(s) -> str: return str(s.lhs) + " := " + str(s.rhs) + ";"

@attrs(frozen=True)
class AstHavoc(AstStmt):
    ids = attrib(type=List[AstId])
    def __str__(s) -> str: return "havoc " + ",".join(map(str, s.ids)) + ";"

# Returns is for now without argument
class AstReturn(AstStmt):
    def __str__(s) -> str: return "return ;"

@attrs(frozen=True)
class AstGoto(AstStmt):
    labels = attrib(type=List[AstId])
    def __str__(s) -> str: return "goto " + ",".join(map(str, s.labels)) + ";"

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

class AstDecl(AstNode): pass

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

# Programs
@attrs(frozen=True)
class AstProgram(AstNode):
    decls = attrib(type=List[AstDecl])
    def __str__(s) -> str: return "\n".join(map(str, s.decls))

def _mkBinExp(lhs: Any, op: Any, rhs: Any) -> AstBinExpr:
  assert isinstance(lhs, AstExpr) and isinstance(rhs, AstExpr) and \
         isinstance(op, str)
  return AstBinExpr(lhs, op, rhs)

T=TypeVar("T")
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

def _toIds(toks: "PR[Any]") -> List[AstId]:
    return [ccast(x, AstId) for x in toks]

class AstBuilder(BoogieParser[AstNode]):
  def onAtom(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 1
    if prod == s.TRUE:
      return [ AstTrue() ]
    elif prod == s.FALSE:
      return [ AstFalse() ]
    elif prod == s.Number:
      return [ AstNumber(int(toks[0])) ]
    else:
      return [ AstId(str(toks[0])) ]

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
    assert isinstance(toks[-1], AstType)
    return [ AstBinding(list(map(str, toks[:-1])), toks[-1]) ]

  # Statements
  def onAssert(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 1 and isinstance(toks[0], AstExpr))
    return [ AstAssert(toks[0]) ]
  def onAssume(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 1 and isinstance(toks[0], AstExpr))
    return [ AstAssume(toks[0]) ]
  def onReturn(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 0)
    return [ AstReturn() ]
  def onGoto(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert(len(toks) > 0)
    return [ AstGoto(_toIds(toks)) ]
  def onAssignment(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) == 2)
    assert (len(toks[0]) == 1)
    assert (len(toks[1]) == 1)
    return [ AstAssignment(toks[0][0], toks[1][0]) ]
  def onHavoc(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert (len(toks) > 0)
    return [ AstHavoc(_toIds(toks)) ]
  def onProgram(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    decls = [ccast(x, AstDecl) for x in toks] # type: List[AstDecl] 
    return [ AstProgram(decls) ]
  def onLocalVarDecl(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 1 and isinstance(toks[0], AstBinding)
    return toks
  def onTypeAtom(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    # Currently only handle ints
    assert len(toks) == 1
    if toks[0] == 'int':
      return [ AstIntType() ]
    elif toks[0] == 'bool':
      return [ AstBoolType() ]
    else:
      raise Exception("NYI type: {}".format(toks[0]))
  def onMapType(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    # Currently only handle ints
    assert len(toks) == 2
    domainT = toks[0]
    rangeT = toks[1]
    assert isinstance(domainT, AstType) and isinstance(rangeT, AstType)
    return [ AstMapType(domainT, rangeT) ]
  def onType(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 1
    return [ ccast(toks[0], AstType) ]
  def onBody(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 2
    return [ AstBody(listify(toks[0]), listify(toks[1])) ]
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
  def onLabeledStatement(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    label = str(toks[0])
    stmt = toks[1]
    assert isinstance(stmt, AstStmt) or isinstance(stmt, AstLabel), "Unexpected {}".format(stmt)
    # TODO: Mypy can't figure out that stmt is of the right type due to above assert
    return [AstLabel(label, stmt)]  #type: ignore
  def onMapIndex(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    mapE = toks[0]
    indexE = toks[1]
    assert isinstance(mapE, AstExpr) and isinstance(indexE, AstExpr)
    return [AstMapIndex(mapE, indexE)]
  def onMapUpdate(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    mapE = toks[0]
    indexE = toks[1]
    newValE = toks[2]
    assert isinstance(mapE, AstExpr) and isinstance(indexE, AstExpr) and isinstance(newValE, AstExpr)
    return [AstMapUpdate(mapE, indexE, newValE)]
  def onQuantified(s, prod: PE, st: str, loc: int, toks: PR) -> Iterable[AstNode]:
    assert len(toks) == 3, "NYI TypeArgs on quantified expressions"
    quantifier = str(toks[0])
    bindings = []  # type: List[AstBinding]
    for node in toks[1]:
        assert isinstance(node, AstBinding)
        bindings.append(node)
    expr = toks[2]
    assert quantifier == "forall", "Existential quantification NYI"
    return [AstForallExpr(bindings, ccast(expr, AstExpr))]

astBuilder = AstBuilder()

def parseExprAst(s: str) -> AstExpr:
  try:
    return ccast(astBuilder.parseExpr(s), AstExpr)
  except:
    print("Failed parsing")
    raise

def parseAst(s: str) -> AstProgram:
  try:
    return ccast(astBuilder.parseProgram(s), AstProgram)
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
        assert isinstance(ast.lhs, AstId)
        return expr_read(ast.rhs)
    elif isinstance(ast, AstHavoc):
        return set()
    else:
        raise Exception("Unknown statement: " + str(ast))

def stmt_changed(ast: AstStmt) -> Set[str]:
    if isinstance(ast, AstLabel):
        ast = ast.stmt

    if isinstance(ast, AstAssignment):
        # Map assignments should be re-written using MapUpdate syntax
        assert isinstance(ast.lhs, AstId), "Bad lhs: {}".format(ast.lhs)
        return set([ast.lhs.name])
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