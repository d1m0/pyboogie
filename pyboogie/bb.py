from .ast import parseAst, AstImplementation, AstLabel, \
        AstAssert, AstAssume, AstHavoc, AstAssignment, AstGoto, \
        AstReturn, AstNode, AstStmt, AstType, AstProgram, AstMapIndex,\
        AstMapUpdate, AstId, parseType, parseStmt, LabelT
from collections import namedtuple
from .util import unique, get_uid, ccast
from typing import Dict, List, Iterable, Tuple, Iterator, Any, Set, Optional
from json import loads

Bindings_T = List[Tuple[str, AstType]]
TypeEnv = Dict[str, AstType]

class BB(List[AstStmt]):
    def __init__(self, label: LabelT, predecessors: Iterable["BB"], stmts: Iterable[AstStmt], successors: Iterable["BB"], internal: bool = False) -> None:
        super().__init__(stmts)
        self.label = label
        self._predecessors = list(predecessors)
        self._successors = list(successors)
        self._internal = internal

    def isInternal(self) -> bool:
        return self._internal

    def predecessors(self) -> List["BB"]:
        return self._predecessors

    def successors(self) -> List["BB"]:
        return self._successors

    def stmts(self) -> List[AstStmt]:
        return list(self)

    def addSuccessor(self, bb: "BB") -> None:
        self._successors.append(bb)
        bb._predecessors.append(self)

    def addPredecessor(self, bb: "BB") -> None:
        bb.addSuccessor(self)

    def isEntry(self) -> bool:
        return len(self._predecessors) == 0

    def isExit(self) -> bool:
        return len(self._successors) == 0

    def __hash__(self) -> int:
        return object.__hash__(self)

    def __str__(self) -> str:
        return self.label + "<[" + ";".join(str(x) for x in self.stmts()) + "]>"

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, BB):
            return False

        return object.__eq__(self, other)

    def to_json(self) -> Any:
        return [self.label,
                [bb.label for bb in self._predecessors],
                [str(stmt) for stmt in self],
                [bb.label for bb in self._successors]]

    @staticmethod
    def from_json(arg: Any) -> Tuple[List[str], "BB", List[str]]:
        raw = loads(arg) if isinstance(arg, str) else arg
        label = raw[0] # type: str
        predLabels = raw[1] # type: List[str]
        stmts = [parseStmt(s) for s in raw[2]] # type: List[AstStmt]
        succLabels = raw[3] # type: List[str]
        return (predLabels, BB(label, [], stmts, []), succLabels)

    def is_gcl(self) -> bool:
        """ A BB is in GCL form if all the assumes come first in the statement
        list, and all of the asserts come last. """
        def stmt_weight(stmt: AstStmt) -> int:
            if isinstance(stmt, AstAssume):
                return 0
            else:
                return 1

        stmt_weights = [stmt_weight(stmt) for stmt in self]
        return stmt_weights == sorted(stmt_weights)

    def is_isomorphic(self, other: "BB", mapping: "Optional[Dict[BB, BB]]" = None) -> bool:
        """ Check if the CFG rooted at self is isomorphic to the CFG rooted at other.
            This involves checking that:
                1) self and other have the same statements
                2) there is a bijection F from self.successors() onto other.successors() such that
                    for all n \in self.successors(), n and F(n) are also isomorphic

            If return is true, mapping at the end holds the mapping from self's cfg to other's.
        """
        if (mapping is None):
            mapping = {}

        if (self in mapping):
            return mapping[self] == other

        mapping[self] = other

        # Check basic shape of BBs equal
        if (self.label != other.label or
            len(self._predecessors) != len(other._predecessors) or
            len(self) != len(other) or
            len(self._successors) != len(other._successors)):
            return False

        # Check statements match up
        for (aStmt, bStmt) in zip(self, other):
            if (aStmt != bStmt):
                return False

        # Since we require BB labels ot be unique in a function, can use them to compute
        # the only possible permutation of successors
        otherSuccs = { x.label: x   for  x in other.successors() } # type: Dict[str, BB]
        for succBB in self.successors():
            if (succBB.label not in otherSuccs or
                not succBB.is_isomorphic(otherSuccs[succBB.label], mapping)):
                return False

        return True

    def pp(self) -> str:
        goto_str = "" if len(self.successors()) == 0 else \
            "\n    goto {};".format(",".join(bb.label for bb in self.successors()))

        return self.label + ":\n" + \
            "\n".join("    " + str(x) for x in self) + goto_str

    def reachable(self) -> Iterable["BB"]:
        reachable = set()  # type: Set[BB]
        workQ = [self]  # type: List[BB]
        while len(workQ) > 0:
            bb = workQ.pop()
            if bb in reachable:
                continue

            reachable.add(bb)
            workQ.extend(bb.successors())

        return reachable

LocT = Tuple[BB, int] # Program location
def prevLocations(l: LocT) -> List[LocT]:
    bb, idx = l
    if (idx > 0):
        return [(bb, idx-1)]

    return [(predBB, len(predBB)) for predBB in bb.predecessors()]

def nextLocations(l: LocT) -> List[LocT]:
    bb, idx = l
    if (idx < len(bb)):
        return [(bb, idx+1)]

    return [(sucBB, 0) for sucBB in bb.successors()]

class Function(object):
    @staticmethod
    def load(filename: str) -> Iterable["Function"]:
        funcs = [] # type: List[Function]
        f = open(filename)
        txt = f.read()
        prog = parseAst(txt) # type: AstProgram
        for decl in prog.decls:
            assert isinstance(decl, AstImplementation)
            funcs.append(Function.build(decl))

        return funcs

    @staticmethod
    def build(fun: AstImplementation) -> "Function":
        # Step 1: Break statements into basic blocks
        bbs = {} # type: Dict[str, BB]
        curLbl = None
        successors = {}  # type: Dict[str, List[str]]
        for stmt in fun.body.stmts:
            # A BB starts with a labeled statment
            while (isinstance(stmt, AstLabel)):
                oldLbl = curLbl
                curLbl = str(stmt.label)
                bbs[curLbl] = BB(curLbl, [], [], [])
                if (oldLbl is not None):
                    assert (oldLbl not in successors)
                    successors[oldLbl] = [curLbl]
                stmt = stmt.stmt

            if (stmt is None):
                assert curLbl != None and len(bbs[curLbl]) == 0 # Empty BB at end
                continue

            if (isinstance(stmt, AstAssert) or
                isinstance(stmt, AstAssume) or
                isinstance(stmt, AstHavoc) or
                isinstance(stmt, AstAssignment)):
                assert (curLbl is not None)
                bbs[curLbl].append(stmt)
            elif (isinstance(stmt, AstGoto)):
                assert (curLbl is not None)
                successors[curLbl] = successors.get(curLbl, []) + list(map(str, stmt.labels))
                curLbl = None
            elif (isinstance(stmt, AstReturn)):
                curLbl = None
            else:
                raise Exception("Unknown statement : " + str(stmt))

        for (lbl, succs) in successors.items():
            bbs[lbl]._successors = [bbs[x] for x in succs]

        for bb in bbs.values():
            for succ in bb.successors():
                succ._predecessors.append(bb)

        parameters = [(name, binding.typ) for binding in fun.parameters for name in binding.names ] # type: Bindings_T
        local_vars = [(name, binding.typ) for binding in fun.body.bindings for name in binding.names ] # type: Bindings_T
        returns = [(name, binding.typ) for binding in fun.returns for name in binding.names ] # type: Bindings_T
        f = Function(fun.name, bbs.values(), parameters, local_vars, returns)

        if len(list(f.exits())) != 1:
            exitBB = BB("__dummy_exit__", [], [], [])

            for bb in f.exits():
                bb.addSuccessor(exitBB)

            f._bbs[exitBB.label] = exitBB

        return f

    def __init__(self, name: str, bbs: Iterable[BB], parameters: Bindings_T, local_vars: Bindings_T, returns: Bindings_T) -> None:
        self.name = name
        self._bbs = {bb.label: bb for bb in bbs}
        self.parameters = parameters
        self.locals = local_vars 
        self.returns = returns
        self._rewrite_assingments()

    def entry(self) -> BB:
        return unique([bb for bb in self._bbs.values() if not bb.isInternal() and bb.isEntry()])

    def exits(self) -> Iterator[BB]:
        return iter([bb for bb in self._bbs.values() if bb.isExit()])

    def exit(self) -> BB:
        return unique(self.exits())

    def bbs(self) -> Iterable[BB]:
        return self._bbs.values()

    def bbs_preorder(self, bb: Optional[BB] = None, visited = None) -> Iterable[BB]:
        if (bb is None):
            bb = self.entry()
            visited = set()

        yield bb

        visited.add(bb)
        for child in bb.successors():
            if (child not in visited):
                self.bbs_preorder(child, visited)


    def bbs_postorder(self, bb: Optional[BB] = None, visited: Optional[Set[BB]] = None) -> Iterable[BB]:
        if (bb is None):
            bb = self.entry()
        if (visited is None):
            visited = set()

        visited.add(bb)
        for child in bb.successors():
            if (child not in visited):
                for t in self.bbs_postorder(child, visited):
                    yield t

        yield bb

    def bbs_rpo(self) -> Iterable[BB]:
        return reversed(list(self.bbs_postorder()))

    def get_bb(self, label: LabelT) -> BB:
        return self._bbs[label]

    def _rewrite_assingments(self) -> None:
        """ Rewrite all assignments of the form:
            a[i] := v;
            to:
            a = a[i:=v];

            This applies to multi-dimensional maps:
            a[i][j] := v;
            to:
            a = a[i:=a[i][j:=v]]
        """
        for bb in self.bbs():
            for stmt_idx in range(len(bb)):
                stmt = bb[stmt_idx]
                if (not isinstance(stmt, AstAssignment)):
                    continue

                lhs = stmt.lhs
                rhs = stmt.rhs

                while (isinstance(lhs, AstMapIndex)):
                    rhs = AstMapUpdate(lhs.map, lhs.index, rhs)
                    assert (isinstance(lhs.map, AstMapIndex) or 
                            isinstance(lhs.map, AstId))
                    lhs = lhs.map

                bb[stmt_idx] = AstAssignment(ccast(lhs, AstId), rhs)

    def to_json(self) -> Any:
        """ Convert self to a JSON-like python object. If you want a string
            just call json.dumps() on return.
        """
        return [
                self.name,
                [(name, str(typ)) for (name, typ) in self.parameters],
                [(name, str(typ)) for (name, typ) in self.locals],
                [(name, str(typ)) for (name, typ) in self.returns],
                [bb.to_json() for bb in self._bbs.values()],
        ]

    @staticmethod
    def from_json(arg: Any) -> "Function":
        """ Given a JSON string, or a pythonified JSON object, returned by f.to_json() for some Function f,
            re-build f
        """
        raw = loads(arg) if isinstance(arg, str) else arg
        name = raw[0]
        parameters = [(x[0], parseType(x[1])) for x in raw[1]]
        locals = [(x[0], parseType(x[1])) for x in raw[2]]
        returns = [(x[0], parseType(x[1])) for x in raw[3]]
        # First parse out BBs, and pred/succ labels
        bbs = []
        for bbJson in raw[4]:
            bbInfo = BB.from_json(bbJson)
            bbs.append(bbInfo)

        # Build map form labels to bbs
        mapping = {bb.label: bb for (_, bb, _) in bbs } # type: Dict[str, BB]

        # Add edges between bbs
        for (_, bb, succLabels) in bbs:
            for succ in succLabels:
                bb.addSuccessor(mapping[succ])

        return Function(name, [bb for (_,bb,_) in bbs], parameters, locals, returns)

    def eq(self, other: "Function") -> bool:
        """ Check structural equality between self and other """
        return (self.name == other.name and
               self.parameters == other.parameters and
               self.locals == other.locals and
               self.returns == other.returns and
               self.entry().is_isomorphic(other.entry()))

    def is_gcl(self) -> bool:
        return all(bb.is_gcl() for bb in self._bbs.values())

    def split_asserts(self) -> Tuple["Function", Dict[BB, BB]]:
        workQ = [(None, self.entry())]  # type: List[Tuple[Optional[BB], BB]]
        bbMap = {}  # type: Dict[BB, BB]

        while len(workQ) > 0:
            (from_bb, cur_bb) = workQ.pop()
            if cur_bb in bbMap: # already visited cur_bb and created a copy
                if from_bb is not None:
                    from_bb._successors.append(bbMap[cur_bb])
                    bbMap[cur_bb]._predecessors.append(from_bb)
                continue

            new_bb = BB(
                cur_bb.label,
                [bbMap[x] for x in cur_bb.predecessors() if x in bbMap],
                [],
                [],
                False,
            )

            for pred in cur_bb.predecessors():
                if pred not in bbMap:
                    continue

                bbMap[pred]._successors.append(new_bb)

            bbMap[cur_bb] = new_bb

            for stmt in cur_bb.stmts():
                if isinstance(stmt, AstAssert):
                    if new_bb.isInternal() and new_bb.label.startswith("_assert_"):
                        new_bb.append(stmt)
                    else:
                        tmp_bb = BB(
                            get_uid("_assert"),
                            [new_bb],
                            [stmt],
                            [],
                            True
                        )
                        new_bb._successors.append(tmp_bb)
                        new_bb = tmp_bb
                else:
                    if new_bb.isInternal() and new_bb.label.startswith("_assert_"):
                        tmp_bb = BB(
                            get_uid("_assign"),
                            [new_bb],
                            [stmt],
                            [],
                            True
                        )
                        new_bb._successors.append(tmp_bb)
                        new_bb = tmp_bb
                    else:
                        new_bb.append(stmt)

            for succ in cur_bb.successors():
                workQ.append((new_bb, succ))

        return (Function(self.name, bbMap[self.entry()].reachable(),
                         self.parameters, self.locals, self.returns), bbMap)

    def pp(self) -> str:
        def pp_bindings(b: Bindings_T) -> str:
            return ",".join("{}:{}".format(str(id), str(typ)) for (id, typ) in b)

        def pp_locals(b: Bindings_T) -> str:
            return "\n".join("    var {}: {};".format(str(id), str(typ)) for (id, typ) in b)

        return "implementation {}({}){}\n{{\n{}\n{}\n}}".format(
            self.name,
            pp_bindings(self.parameters),
            (" returns({})".format(pp_bindings(self.returns)) if len(self.returns) > 0 else ""),
            pp_locals(self.locals),
            "\n\n".join(bb.pp() for bb in self._bbs.values()))

    def getTypeEnv(self) -> TypeEnv:
        return { name: typ for (name, typ) in self.parameters + self.returns + self.locals }