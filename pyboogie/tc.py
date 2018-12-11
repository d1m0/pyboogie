# Types
from .ast import AstIntType, AstBoolType, AstBVType, AstMapType, AstCompoundType
# Expressions
from .ast import AstExpr, AstFalse, AstTrue, AstNumber, AstId, AstWildcard,\
        AstMapIndex, AstMapUpdate, AstUnExpr, AstBinExpr, AstTernary,\
        AstForallExpr, AstFuncExpr
# Statements
from .ast import AstStmt, AstLabel, AstOneExprStmt, AstAssignment, \
        AstHavoc, AstReturn, AstGoto, AstCall
# Declarations
from .ast import AstProgram, AstProcedure, AstFunctionDecl, AstImplementation,\
        AstDecl, AstBinding, AstNode, AstType, AstTypeConstructorDecl, \
        AstBody, AstVarDecl, AstConstDecl, AstAxiomDecl
from typing import Union, Tuple, Optional, Any, Dict, Iterable, Generic, TypeVar, List

AstScope=Union[AstProgram, AstBody]

class Singleton:
    def __eq__(self, other):
        return isinstance(other, self.__class__)
    def __hash__(self):
        return 42

# Types:
class BType:    pass
class BInt(BType, Singleton):
    def __str__(self):  return "int"
class BBool(BType, Singleton):
    def __str__(self):  return "bool"
class BBV(BType):
    def __init__(self, nbits: int):
        self._nbits = nbits
    def __eq__(self, other):
        return isinstance(other, BBV) and self._nbits == other._nbits
    def __hash__(self):
        return hash(self._nbits)
    def __str__(self):  return "bv{}".format(self._nbits)
class BMap(BType):
    def __init__(self, domain: List[BType], range: BType):
        self._domain = domain
        self._range = range
    def __eq__(self, other):
        return isinstance(other, BMap) and \
                self._domain == other._domain and \
                self._range == other._range
    def __hash__(self):
        return hash((self._domain, self._range))
    def __str__(self):
        return "[{}]{}".format(str(self._domain), str(self._range))
class BLambda(BType):
    def __init__(self, args: Tuple[BType,...], ret: BType):
        self._args = args
        self._return = ret
    def __eq__(self, other):
        return isinstance(other, BLambda) and \
                self._args == other._args and \
                self._return == other._return
    def __hash__(self):
        return hash((self._args, self._return))
    def __str__(self):
        return "[{}]{}".format(",".join(map(str, self._args)), str(self._return))
class BProcedure(BType):
    """ Type of a procedure. Only used internally - not an actual type in
        Boogie's type system. """
    def __init__(self, args: Tuple[BType,...], rets: Tuple[BType, ...]):
        self._args = args
        self._returns = rets
    def __eq__(self, other):
        return isinstance(other, BProcedure) and \
                self._args == other._args and \
                self._returns == other._returns
    def __hash__(self):
        return hash((self._args, self._returns))
    def __str__(self):
        return "[{}]{}".format(str(self._args), str(self._returns))
# TODO: User defined types

class TypeError(Exception):
    def __init__(self, loc, msg: str):
        self._loc = loc;
        self._msg = msg;

    def __str__(self):
        return "TypeError in " + str(self._loc) + ": " + self._msg;


Declaration=Union[AstDecl, AstBinding]

ScopeT=TypeVar("ScopeT")
DeclT=TypeVar("DeclT")
class Scope(Generic[ScopeT, DeclT]):
    def __init__(self, astRoot: ScopeT, parent: Optional["Scope"]):
        self._root = astRoot
        self._parent = parent
        self._bindings: Dict[str, DeclT] = {}

    def define(self, Id: str, typ: DeclT):
        if (Id in self._bindings):
            raise TypeError(self._root, "{} defined more than once".format(Id))

        self._bindings[Id] = typ;

    def lookup(self, Id: str) -> Optional[DeclT]:
        if Id in self._bindings:
            return self._bindings[Id]

        if (self._parent is not None):
            return self._parent.lookup(Id)

        return None


# Per krml178 p.4: There are 5 independent scopes:
# Types are defined only at the Program level.
# TODO: Update to support TypeSynonyms
TypeScope=Scope[AstProgram, AstTypeConstructorDecl]
# Function names are also defined at the Program level
FunctionScope=Scope[AstProgram, BLambda]
# Constants and Variables can be defined at the Program or Procedure/Function
# lvl
VarScope=Scope[Union[AstProgram, AstFunctionDecl, AstProcedure, AstImplementation, AstForallExpr], BType]
# Procedures can be defined at the Program level
ProcedureScope=Scope[Union[AstProgram], BProcedure]
# Attributes don't have definition statements so we don't track them
# Our type-checking environment is a tuple of the 4 different scopes
TCEnv=Tuple[TypeScope, FunctionScope, VarScope, ProcedureScope]


def flatBindings(bindings: Iterable[AstBinding]) -> Iterable[Tuple[str, AstType]]:
    for b in bindings:
        for name in b.names:
            yield (name, b.typ)

def tcType(node: AstType, env: TCEnv) -> BType:
    """ Type check a type specification in a given environment. Check that any
        identifiers in type constructors are in-scope and number of type
        arguments for type constructors respect user definitions. Raise an 
        error on failure. Return the checked BType on success."""
    if (isinstance(node, AstIntType)):
        return BInt()
    elif (isinstance(node, AstBoolType)):
        return BBool()
    elif (isinstance(node, AstBVType)):
        return BBV(node.numBits)
    elif (isinstance(node, AstMapType)):
        assert len(node.typeVars) == 0, "NYI Poly-maps"
        domainT = [tcType(indT, env) for indT in node.domainT]
        rangeT = tcType(node.rangeT, env)
        return BMap(domainT, rangeT)
    elif (isinstance(node, AstCompoundType)):
        assert False, "NYI Compound types"
    else:
        assert False, "Unknown type: {}".format(node)

def tcExpr(node: AstExpr, env: TCEnv) -> BType:
    """ Type check an expression in a given environment and return the type of
        the expression. Raise a TypeError on failure """
    (types, funcs, vars, procs) = env
    if isinstance(node, AstFalse) or isinstance(node, AstTrue):
        return BBool()
    elif isinstance(node, AstNumber):
        return BInt()
    elif isinstance(node, AstId):
        idT = vars.lookup(node.name)
        if idT is None:
            raise TypeError(node, "Unknown var {}".format(node.name))
        return idT
    elif isinstance(node, AstWildcard):
        # TODO: Revisit after call-forall
        return BBool()
    elif isinstance(node, AstMapIndex):
        tMap: BType = tcExpr(node.map, env)
        tIndex: List[BType] = [tcExpr(node.index, env)]
        if (not isinstance(tMap, BMap)):
            raise TypeError(node, "Expected map here {} instead got {}".format(node, tMap))

        if tIndex != tMap._domain:
            raise TypeError(node, "Bad type for index in {} expected {} but got {}".format(node, tMap._domain, tIndex))

        return tMap._range
    elif isinstance(node, AstMapUpdate):
        tMap = tcExpr(node.map, env)
        tIndex = [tcExpr(node.index, env)]
        tVal = tcExpr(node.newVal, env)

        if (not isinstance(tMap, BMap)):
            raise TypeError(node, "Expected map here {} instead got {}".format(node, tMap))

        if tIndex != tMap._domain:
            raise TypeError(node, "Bad type for index in {} expected {} but got {}".format(node, tMap._domain, tIndex))

        if tVal != tMap._range:
            raise TypeError(node, "Bad type for value in map update {} expected {} but got {}".format(node, tMap._range, tVal))

        return tMap
    elif isinstance(node, AstUnExpr):
        argT = tcExpr(node.expr, env)
        if (node.op == '!'):
            if  (argT != BBool()):
                raise TypeError(node, "Expected boolean instead got {}".format(node.expr))
            return BBool()
        elif (node.op == '-'):
            if (argT != BInt()):
                raise TypeError(node, "Expected int instead got {}".format(node.expr))
            return BInt()
        else:
            assert False, "Bad unary op {}".format(node.op)
    elif isinstance(node, AstBinExpr):
        lhsT = tcExpr(node.lhs, env)
        rhsT = tcExpr(node.rhs, env)

        if (node.op in ['+', '-', '*', '/', 'div', 'mod']):
            if lhsT != BInt() or rhsT != BInt():
                raise TypeError(node, "Bad args to {} in {}. Expect ints".format(node.op, node))
            return BInt()
        elif (node.op in ['!=', '<=', '>=', '<:', '==', '<', '>']):
            if lhsT != BInt() or rhsT != BInt():
                raise TypeError(node, "Bad args to {} in {}. Expect ints".format(node.op, node))
            return BBool()
        elif (node.op in ['<===>', '==>', '||', '&&']):
            if lhsT != BBool() or rhsT != BBool():
                raise TypeError(node, "Bad args to {} in {}. Expect bools".format(node.op, node))
            return BBool()
        else:
            assert False, "Bad op {}".format(node.op)
    elif isinstance(node, AstTernary):
        condT = tcExpr(node.condition, env)
        thenT = tcExpr(node.thenE, env)
        elseT = tcExpr(node.elseE, env)

        if (condT != BBool()):
            raise TypeError(node, "Ternary requires bool not {} in {}".format(condT, node))
        if (thenT != elseT):
            raise TypeError(node, "Ternary types disagree: {} and {}".format(thenT, elseT))

        return thenT
    elif isinstance(node, AstForallExpr):
        newVars: VarScope = Scope(node, vars)
        for b in node.bindings:
            for name in b.names:
                newVars.define(name, tcType(b.typ, env))
        newEnv = (types, funcs, newVars, procs)
        return tcExpr(node.expr, newEnv)
    elif isinstance(node, AstFuncExpr):
        argTypes = tuple([tcExpr(arg, env) for arg in node.ops])
        funType: Optional[BType] = funcs.lookup(node.funcName)
        if (funType is None or not isinstance(funType, BLambda)):
            raise TypeError(node, "{} does not name a function".format(node.funcName))

        if argTypes != funType._args:
            raise TypeError(node, "Argument mismatch in call {}".format(node))

        return funType._return
    else:
        assert False, "Unknown expr: {}".format(node)
        

def tcStmt(node: AstStmt, env: TCEnv) -> None:
    """ Type check a statement in a given environment. Raise a TypeError on
        failure. """
    (types, funcs, vars, procs) = env
    if (isinstance(node, AstLabel)):
        # TODO: TC Labels
        tcStmt(node.stmt, env)
    elif (isinstance(node, AstOneExprStmt)):
        exprType = tcExpr(node.expr, env)
        if (exprType != BBool()):
            raise TypeError(node, "Expected boolean expression in {}".format(node))
    elif (isinstance(node, AstAssignment)):
        lhsTypes = [tcExpr(lhsId, env) for lhsId in node.lhs]
        rhsTypes = [tcExpr(rhsId, env) for rhsId in node.rhs]

        if (lhsTypes != rhsTypes):
            raise TypeError(node, "Type mismatch in assignment {}".format(node))
    elif (isinstance(node, AstHavoc)):
        for id in node.ids:
            tcExpr(id, env)
    elif (isinstance(node, AstReturn)):
        pass
    elif (isinstance(node, AstGoto)):
        pass
    elif (isinstance(node, AstCall)):
        procType: Optional[BType] = procs.lookup(node.id)

        if (procType is None):
            raise TypeError(node, "Unknown procedure {} in call {}".format(node.id, node))

        if (not isinstance(procType, BProcedure)):
            raise TypeError(node, "{} not a procedure in call {}".format(node.id, node))

        if (node.lhs is None):
            expectedReturns: Tuple[BType,...] = ()
        else:
            expectedReturns = tuple([tcExpr(lhs, env) for lhs in node.lhs])

        arguments = tuple([tcExpr(arg, env) for arg in node.arguments])

        if (procType._args != arguments):
            raise TypeError(node, "Mismatch in arguments in call {}".format(node.id, node))

        if (procType._returns != expectedReturns):
            raise TypeError(node, "Mismatch in arguments in call {}".format(node.id, node))
    else:
        assert False, "Unknown stmt: {}".format(node)


def tcDecl(d: AstDecl, env: TCEnv) -> None:
    """ Type check a declaration in a given environment. DESTRUCTIVELY Update
        the passed-in environment in-place.
    """
    (types, funcs, vars, procs) = env
    if (isinstance(d, AstTypeConstructorDecl)):
        assert False, "NYI Type constructor decls"
    elif (isinstance(d, AstVarDecl) or isinstance(d, AstConstDecl)):
        # Nothing to check - just add new global vars to environment
        for name in d.binding.names:
            vars.define(name, tcType(d.binding.typ, env))
    elif (isinstance(d, AstFunctionDecl)):
        newFunT = BLambda(
            tuple(tcType(b.typ, env) for b in d.parameters for name in b.names),
            tcType(d.returns, env))
        funcs.define(d.id, newFunT)

        if (d.body is not None):
            # Check function body in new scope with parameters declared
            bodyVars: VarScope = Scope(d, vars)
            for (name, typ) in flatBindings(d.parameters):
                bodyVars.define(name, tcType(typ, env))

            bodyEnv = (types, funcs, bodyVars, procs)
            retT = tcExpr(d.body, bodyEnv)

            # Check type of body agrees with return type
            if retT != newFunT._return:
                raise TypeError(d, "Return type mismatch in {}".format(d))
    elif (isinstance(d, AstProcedure) or isinstance(d, AstImplementation)):
        procOrImpl: Union[AstProcedure, AstImplementation] = d
        params = procOrImpl.parameters
        rets = procOrImpl.returns
        if procOrImpl.body is not None:
            localVars: List[AstBinding] = procOrImpl.body.bindings
        else:
            localVars = []

        implT = BProcedure(
            tuple(tcType(typ, env) for (_, typ) in flatBindings(params)),
            tuple(tcType(typ, env) for (_, typ) in flatBindings(rets)))

        # First check implementation agrees with corresponding procedure
        if (isinstance(d, AstImplementation)):
            procT = procs.lookup(d.name)
            if procT is None:
                raise TypeError(d, "Implementaion {} missing procedure definition".format(d.name))
            if (procT != implT):
                raise TypeError(d, "Implementaion {} disagrees with procedure".format(d.name))
        else:
            if procs.lookup(d.name) is not None:
                raise TypeError(d, "Multiple procedures with same name {}".format(d.name))


        bodyVars = Scope(procOrImpl, vars)
        for (name, typ) in flatBindings(params):
            bodyVars.define(name, tcType(typ, env))
        for (name, typ) in flatBindings(rets):
            bodyVars.define(name, tcType(typ, env))

        if (isinstance(d, AstProcedure)):
            reqEnsEnv = (types, funcs, bodyVars, procs)
            # We check requires/ensures in the environment
            # including only parameters and returns
            for (_, expr) in d.requires + d.ensures:
                predT = tcExpr(expr, reqEnsEnv)
                if (predT != BBool()):
                    raise TypeError(d, "Require/ensure not a boolean")

            # Only check modifies in the global variable environment
            for (_, var) in d.modifies:
                if (vars.lookup(var.name) is None):
                    raise TypeError(d, "Unknown var in modifies: {}".format(var))

            procs.define(d.name, implT)

        if (procOrImpl.body is not None):
            for (name, typ) in flatBindings(localVars):
                bodyVars.define(name, tcType(typ, env))

            bodyEnv = (types, funcs, bodyVars, procs)
            for stmt in procOrImpl.body.stmts:
                tcStmt(stmt, bodyEnv)
    elif isinstance(d, AstAxiomDecl):
        tcExpr(d.expr, env)
    else:
        raise TypeError(d, "Don't know how to handle decl of type {}: {}".format(type(d), d))

def tcProg(p: AstProgram) -> TCEnv:
    typeScope: TypeScope = Scope(p, None)
    funScope: FunctionScope = Scope(p, None)
    varScope: VarScope = Scope(p, None)
    procScope: ProcedureScope = Scope(p, None)

    env = (typeScope, funScope, varScope, procScope)
    for d in p.decls:
        tcDecl(d, env)

    return env
