# Types
from .ast import AstIntType, AstBoolType, AstBVType, AstMapType,\
        AstCompoundType
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
from typing import Union, Tuple, Optional, Any, Dict, Iterable, Generic, \
        TypeVar, List, Callable


class Singleton:
    def __eq__(self, other):
        return isinstance(other, self.__class__)

    def __hash__(self):
        return 42


class BType:
    """ Boogie types base type """
    pass


class BInt(BType, Singleton):
    def __str__(self): return "int"


class BBool(BType, Singleton):
    def __str__(self): return "bool"


class BBV(BType):
    def __init__(self, nbits: int) -> None:
        self._nbits = nbits

    def __eq__(self, other):
        return isinstance(other, BBV) and self._nbits == other._nbits

    def __hash__(self):
        return hash(self._nbits)

    def __str__(self): return "bv{}".format(self._nbits)


class BMap(BType):
    def __init__(self, domain: List[BType], range: BType) -> None:
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
    def __init__(self, args: Tuple[BType, ...], ret: BType) -> None:
        self._args = args
        self._return = ret

    def __eq__(self, other):
        return isinstance(other, BLambda) and \
                self._args == other._args and \
                self._return == other._return

    def __hash__(self):
        return hash((self._args, self._return))

    def __str__(self):
        return "[{}]{}".format(
                ",".join(map(str, self._args)),
                str(self._return))


class BProcedure(BType):
    """ Type of a procedure. Only used internally - not an actual type in
        Boogie's type system. """
    def __init__(self, args: Tuple[BType, ...], rets: Tuple[BType, ...]) -> None:
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


class BUserType(BType):
    """ Type of a procedure. Only used internally - not an actual type in
        Boogie's type system. """
    def __init__(self, name: str, args: Tuple[BType, ...]) -> None:
        self._name = name
        self._args = args

    def __eq__(self, other):
        return isinstance(other, BUserType) and \
                self._name == other._name and \
                self._args == other._args

    def __hash__(self):
        return hash((self._name, self._args))

    def __str__(self):
        return "{} {}".format(self._name, " ".join(map(str, self._args)))


class BTypeError(Exception):
    def __init__(self, loc, msg: str) -> None:
        self._loc = loc
        self._msg = msg

    def __str__(self):
        return "BTypeError in " + str(self._loc) + ": " + self._msg


ScopeModifierNodes = Union[AstProgram, AstFunctionDecl, AstProcedure, AstImplementation, AstForallExpr]
T = TypeVar("T")


class BoogieScope:
    def __init__(
            self,
            root: ScopeModifierNodes,
            parent: Optional["BoogieScope"]) -> None:

        # Per krml178 p.4: There are 4 independent scopes: Types are defined
        # only at the Program level. We don't count the attribute namespace
        # here
        # TODO: Update to support TypeSynonyms
        typeScope: Dict[str, AstTypeConstructorDecl] = {}
        funScope: Dict[str, BLambda] = {}
        varScope: Dict[str, BType] = {}
        procScope: Dict[str, BProcedure] = {}
        self._parent = parent
        self._root = root

        if (isinstance(root, AstProgram)):
            assert parent is None
        elif (isinstance(root, AstFunctionDecl) or
              isinstance(root, AstProcedure) or
              isinstance(root, AstImplementation) or
              isinstance(root, AstForallExpr)):
            assert parent is not None
            typeScope = parent._typeScope
            funScope = parent._funScope
            procScope = parent._procScope
        else:
            assert False, "NYI Scope root {}".format(root)

        self._typeScope: Dict[str, AstTypeConstructorDecl] = typeScope
        self._funScope: Dict[str, BLambda] = funScope
        self._varScope: Dict[str, BType] = varScope
        self._procScope: Dict[str, BProcedure] = procScope

    def _define(self, Id: str, obj: T, mapping: Dict[str, T]):
        if (Id in mapping):
            raise BTypeError(self._root,
                             "{} defined more than once".format(Id))

        mapping[Id] = obj

    def defType(self, name: str, typ: AstTypeConstructorDecl):
        self._define(name, typ, self._typeScope)

    def lookupType(self, name: str) -> Optional[AstTypeConstructorDecl]:
        if (name in self._typeScope):
            return self._typeScope[name]

        if (self._parent is not None):
            return self._parent.lookupType(name)

        return None

    def defFun(self, name: str, typ: BLambda):
        self._define(name, typ, self._funScope)

    def lookupFun(self, name: str) -> Optional[BLambda]:
        if (name in self._funScope):
            return self._funScope[name]

        if (self._parent is not None):
            return self._parent.lookupFun(name)

        return None

    def defVar(self, name: str, typ: BType):
        self._define(name, typ, self._varScope)

    def lookupVar(self, name: str) -> Optional[BType]:
        if (name in self._varScope):
            return self._varScope[name]

        if (self._parent is not None):
            return self._parent.lookupVar(name)

        return None

    def defProc(self, name: str, typ: BProcedure):
        self._define(name, typ, self._procScope)

    def lookupProc(self, name: str) -> Optional[BProcedure]:
        if (name in self._procScope):
            return self._procScope[name]

        if (self._parent is not None):
            return self._parent.lookupProc(name)

        return None


def flatBindings(bindings: Iterable[AstBinding]) -> Iterable[Tuple[str, AstType]]:
    for b in bindings:
        for name in b.names:
            yield (name, b.typ)


def tcType(node: AstType, env: BoogieScope) -> BType:
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
        typConstr = env.lookupType(node.name)
        if (typConstr is None):
            raise BTypeError(
                    node,
                    "Unknown user defined type {}".format(node.name))

        typeArgs = [tcType(tArg, env) for tArg in node.typeArgs]
        formalArity = len(typConstr.formals)
        actualArity = len(typeArgs)
        if (actualArity != formalArity):
            raise BTypeError(
                    node,
                    "Expected {} arguments for {} but got {}".format(
                        formalArity,
                        node.name,
                        actualArity))

        return BUserType(node.name, tuple(typeArgs))
    else:
        assert False, "Unknown type: {}".format(node)


def tcExpr(node: AstExpr, env: BoogieScope) -> BType:
    """ Type check an expression in a given environment and return the type of
        the expression. Raise a BTypeError on failure """
    if isinstance(node, AstFalse) or isinstance(node, AstTrue):
        return BBool()
    elif isinstance(node, AstNumber):
        return BInt()
    elif isinstance(node, AstId):
        idT = env.lookupVar(node.name)
        if idT is None:
            raise BTypeError(node, "Unknown var {}".format(node.name))
        return idT
    elif isinstance(node, AstWildcard):
        # TODO: Revisit after call-forall
        return BBool()
    elif isinstance(node, AstMapIndex):
        tMap: BType = tcExpr(node.map, env)
        tIndex: List[BType] = [tcExpr(node.index, env)]
        if (not isinstance(tMap, BMap)):
            raise BTypeError(
                    node,
                    "Expected map here {} instead got {}".format(node, tMap))

        if tIndex != tMap._domain:
            raise BTypeError(
                    node,
                    "Bad type for index in {} expected {} but got {}".format(
                        node, tMap._domain, tIndex))

        return tMap._range
    elif isinstance(node, AstMapUpdate):
        tMap = tcExpr(node.map, env)
        tIndex = [tcExpr(node.index, env)]
        tVal = tcExpr(node.newVal, env)

        if (not isinstance(tMap, BMap)):
            raise BTypeError(
                    node,
                    "Expected map here {} instead got {}".format(node, tMap))

        if tIndex != tMap._domain:
            raise BTypeError(
                    node,
                    "Bad type for index in {} expected {} but got {}".format(
                        node, tMap._domain, tIndex))

        if tVal != tMap._range:
            raise BTypeError(
                    node,
                    "Bad type for value in map update {} expected {} but got {}".format(
                        node, tMap._range, tVal))

        return tMap
    elif isinstance(node, AstUnExpr):
        argT = tcExpr(node.expr, env)
        if (node.op == '!'):
            if (argT != BBool()):
                raise BTypeError(
                        node,
                        "Expected boolean instead got {}".format(node.expr))
            return BBool()
        elif (node.op == '-'):
            if (argT != BInt()):
                raise BTypeError(
                        node,
                        "Expected int instead got {}".format(node.expr))
            return BInt()
        else:
            assert False, "Bad unary op {}".format(node.op)
    elif isinstance(node, AstBinExpr):
        lhsT = tcExpr(node.lhs, env)
        rhsT = tcExpr(node.rhs, env)

        if (node.op in ['+', '-', '*', '/', 'div', 'mod']):
            if lhsT != BInt() or rhsT != BInt():
                raise BTypeError(
                        node,
                        "Bad args to {} in {}. Expect ints".format(
                            node.op, node))
            return BInt()
        elif (node.op in ['!=', '<=', '>=', '<:', '==', '<', '>']):
            if lhsT != rhsT:
                raise BTypeError(
                        node,
                        "Bad args to {} in {}. Expect same types".format(
                            node.op, node))
            return BBool()
        elif (node.op in ['<===>', '==>', '||', '&&']):
            if lhsT != BBool() or rhsT != BBool():
                raise BTypeError(
                        node,
                        "Bad args to {} in {}. Expect bools".format(
                            node.op, node))
            return BBool()
        else:
            assert False, "Bad op {}".format(node.op)
    elif isinstance(node, AstTernary):
        condT = tcExpr(node.condition, env)
        thenT = tcExpr(node.thenE, env)
        elseT = tcExpr(node.elseE, env)

        if (condT != BBool()):
            raise BTypeError(
                    node,
                    "Ternary requires bool not {} in {}".format(condT, node))
        if (thenT != elseT):
            raise BTypeError(
                    node,
                    "Ternary types disagree: {} and {}".format(thenT, elseT))

        return thenT
    elif isinstance(node, AstForallExpr):
        newEnv = BoogieScope(node, env)
        for b in node.bindings:
            for name in b.names:
                newEnv.defVar(name, tcType(b.typ, env))
        return tcExpr(node.expr, newEnv)
    elif isinstance(node, AstFuncExpr):
        argTypes = tuple([tcExpr(arg, env) for arg in node.ops])
        funType: Optional[BType] = env.lookupFun(node.funcName)
        if (funType is None or not isinstance(funType, BLambda)):
            raise BTypeError(
                    node,
                    "{} does not name a function".format(node.funcName))

        if argTypes != funType._args:
            raise BTypeError(node, "Argument mismatch in call {}".format(node))

        return funType._return
    else:
        assert False, "Unknown expr: {}".format(node)


def tcStmt(node: AstStmt, env: BoogieScope) -> None:
    """ Type check a statement in a given environment. Raise a BTypeError on
        failure. """
    if (isinstance(node, AstLabel)):
        # TODO: TC Labels
        tcStmt(node.stmt, env)
    elif (isinstance(node, AstOneExprStmt)):
        exprType = tcExpr(node.expr, env)
        if (exprType != BBool()):
            raise BTypeError(
                    node,
                    "Expected boolean expression in {}".format(node))
    elif (isinstance(node, AstAssignment)):
        lhsTypes = [tcExpr(lhsId, env) for lhsId in node.lhs]
        rhsTypes = [tcExpr(rhsId, env) for rhsId in node.rhs]

        if (lhsTypes != rhsTypes):
            raise BTypeError(
                    node,
                    "Type mismatch in assignment {}".format(node))
    elif (isinstance(node, AstHavoc)):
        for id in node.ids:
            tcExpr(id, env)
    elif (isinstance(node, AstReturn)):
        pass
    elif (isinstance(node, AstGoto)):
        pass
    elif (isinstance(node, AstCall)):
        procType: Optional[BType] = env.lookupProc(node.id)

        if (procType is None):
            raise BTypeError(
                    node,
                    "Unknown procedure {} in call {}".format(node.id, node))

        if (not isinstance(procType, BProcedure)):
            raise BTypeError(
                    node,
                    "{} not a procedure in call {}".format(node.id, node))

        if (node.lhs is None):
            expectedReturns: Tuple[BType, ...] = ()
        else:
            expectedReturns = tuple([tcExpr(lhs, env) for lhs in node.lhs])

        arguments = tuple([tcExpr(arg, env) for arg in node.arguments])

        if (procType._args != arguments):
            raise BTypeError(
                    node,
                    "Mismatch in arguments in call {}".format(node.id, node))

        if (procType._returns != expectedReturns):
            raise BTypeError(
                    node,
                    "Mismatch in arguments in call {}".format(node.id, node))
    else:
        assert False, "Unknown stmt: {}".format(node)


def typeAccumulate(d: AstDecl, env: BoogieScope) -> None:
    """ Accumulate definitions in the current environment from the definition
        d. Destructively updates the passed-in environment in-place.
    """
    if (isinstance(d, AstTypeConstructorDecl)):
        if env.lookupType(d.name) is not None:
            raise BTypeError(d, "Type {} defined twice".format(d.name))

        env.defType(d.name, d)
    elif (isinstance(d, AstVarDecl) or isinstance(d, AstConstDecl)):
        for name in d.binding.names:
            if env.lookupVar(name) is not None:
                raise BTypeError(d, "Var {} defined twice".format(name))

            env.defVar(name, tcType(d.binding.typ, env))
    elif (isinstance(d, AstFunctionDecl)):
        if env.lookupFun(d.id) is not None:
            raise BTypeError(d, "Function {} defined twice".format(d.id))

        newFunT = BLambda(
            tuple(tcType(b.typ, env) for b in d.parameters for name in b.names),
            tcType(d.returns, env))

        env.defFun(d.id, newFunT)
    elif (isinstance(d, AstProcedure)):
        if (env.lookupProc(d.name) is not None):
            raise BTypeError(
                    d,
                    "Procedure {} defined more than once".format(d.name))

        procT = BProcedure(
            tuple(tcType(typ, env) for (_, typ) in flatBindings(d.parameters)),
            tuple(tcType(typ, env) for (_, typ) in flatBindings(d.returns)))
        env.defProc(d.name, procT)
    elif (isinstance(d, AstImplementation)):
        pass  # Implementation don't add names to the proc space
    elif (isinstance(d, AstAxiomDecl)):
        pass  # Axioms are anonymous
    else:
        raise BTypeError(
                d,
                "Don't know how to handle decl of type {}: {}".format(
                    type(d), d))


def tcDecl(d: AstDecl, env: BoogieScope) -> None:
    """ Type check a declaration in a given environment. Does not update the
        passed-in environment.
    """
    if (isinstance(d, AstTypeConstructorDecl)):
        pass
    elif (isinstance(d, AstVarDecl) or isinstance(d, AstConstDecl)):
        pass
    elif (isinstance(d, AstFunctionDecl)):
        newFunT = BLambda(
            tuple(tcType(b.typ, env) for b in d.parameters for name in b.names),
            tcType(d.returns, env))

        if (d.body is not None):
            # Check function body in new scope with parameters declared
            newEnv = BoogieScope(d, env)
            for (name, typ) in flatBindings(d.parameters):
                newEnv.defVar(name, tcType(typ, env))

            retT = tcExpr(d.body, newEnv)

            # Check type of body agrees with return type
            if retT != newFunT._return:
                raise BTypeError(d, "Return type mismatch in {}".format(d))
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
            procT = env.lookupProc(d.name)
            if procT is None:
                raise BTypeError(
                        d,
                        "Implementaion {} missing procedure definition".format(
                            d.name))

            if (procT != implT):
                raise BTypeError(
                        d,
                        "Implementaion {} disagrees with procedure".format(
                            d.name))

        newEnv = BoogieScope(procOrImpl, env)

        for (name, typ) in flatBindings(params):
            newEnv.defVar(name, tcType(typ, env))
        for (name, typ) in flatBindings(rets):
            newEnv.defVar(name, tcType(typ, env))

        if (isinstance(d, AstProcedure)):
            # We check requires/ensures in the environment
            # including only parameters and returns
            for (_, expr) in d.requires + d.ensures:
                predT = tcExpr(expr, newEnv)
                if (predT != BBool()):
                    raise BTypeError(d, "Require/ensure not a boolean")

            # Only check modifies in the global variable environment
            for (_, var) in d.modifies:
                if (env.lookupVar(var) is None):
                    raise BTypeError(
                            d,
                            "Unknown var in modifies: {}".format(var))

        if (procOrImpl.body is not None):
            for (name, typ) in flatBindings(localVars):
                newEnv.defVar(name, tcType(typ, env))

            for stmt in procOrImpl.body.stmts:
                tcStmt(stmt, newEnv)
    elif isinstance(d, AstAxiomDecl):
        tcExpr(d.expr, env)
    else:
        raise BTypeError(
                d,
                "Don't know how to handle decl of type {}: {}".format(
                    type(d), d))


def tcProg(p: AstProgram) -> BoogieScope:
    env = BoogieScope(p, None)

    # First accumulate just the type definitions
    for d in p.decls:
        if (not isinstance(d, AstTypeConstructorDecl)):
            continue
        typeAccumulate(d, env)

    # Next accumulate remaining definitions
    for d in p.decls:
        if (isinstance(d, AstTypeConstructorDecl)):
            continue
        typeAccumulate(d, env)

    # Finally check all definitions in the body w.r.t. accumulated env.
    for d in p.decls:
        tcDecl(d, env)

    return env
