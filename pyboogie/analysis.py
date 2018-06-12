from copy import copy
from .bb import Function, BB, LocT, prevLocations, nextLocations
from .ast import AstAssert, AstAssume, AstHavoc, \
        AstAssignment, stmt_read, stmt_changed, AstBinExpr, expr_read,\
        AstStmt, AstExpr, AstId, LabelT
from functools import reduce
from typing import TypeVar, Callable, Dict, Iterable, Set, Optional, Tuple, List
from .util import unique

StateT=TypeVar("StateT")
# A state-transformer function computes a new StateT for a node (AstStmt),
# given the old StateT.
TransformerT = Callable[[AstStmt, StateT], StateT]
# A TransformerMap specifies the transformer function for each type of
# ast statement.
TransformerMapT = Dict[type, TransformerT]
UnionT = Callable[[StateT, StateT], StateT]
# DataFlow state is a mapping from program location to state at that location
# For a BB 'A', and a state S, S['A', 0] described the state
# before the first instruction in 'A'. If 'A' has n instructions S['A', n-1]
# described the state before the last instruction in 'A' and S['A', n]
# describes the state after it - i.e. the state after 'A' completes.
DFlowStateT = Dict[LocT, StateT]

def dataflow(fun: Function, transformerMap: TransformerMapT, unionF: UnionT, bottom: StateT, start: StateT, forward: bool) -> DFlowStateT:
    # Start with all locations mapped to bottom
    state = { (bb, idx): copy(bottom) for bb in fun.bbs() for idx in range(len(bb)+1)} # type: DFlowStateT

    # Compute the first entry on the worklist - entry or exit of CFG depending on forward argument
    if (forward):
        entryLoc = (fun.entry(), 0)
        wList = [ (bb, (0 if forward else len(bb))) for bb in fun.bbs_preorder() ]
    else:
        exitBl = fun.exit()
        entryLoc = (exitBl, len(exitBl))
        wList = [ (bb, (0 if forward else len(bb))) for bb in fun.bbs_rpo() ]

    state[entryLoc] = start

    inList = set(wList)

    nextLocsFunc = nextLocations if forward else prevLocations # type: Callable[[LocT], List[LocT]]

    while len(wList) > 0:
        curLoc = wList.pop()
        inList.remove(curLoc)

        curBB, curIdx = curLoc
        inState = state[curLoc]
        outLabels = nextLocsFunc(curLoc)
        stmt : Optional[AstStmt] = None

        if (forward and curIdx < len(curBB)):
            stmt = curBB[curIdx]
        elif (not forward and curIdx > 0):
            stmt = curBB[curIdx-1]

        if (stmt is not None):
            # Propagating new state across a stmt inside a BB. Run the transformer function
            assert(len(outLabels) == 1)
            outState = transformerMap[stmt.__class__](stmt, inState)
            nextLoc : LocT = unique(outLabels)
            if (state[nextLoc] != outState):
                state[nextLoc] = outState
                if (nextLoc not in inList):
                    wList.append(nextLoc)
                    inList.add(nextLoc)
        else:
            # Propagating new state across edges between BBs.
            outState = inState
            for l in outLabels:
                updatedOutState = unionF(state[l], outState)

                if (updatedOutState != state[l]):
                    state[l] = updatedOutState
                    if (l not in inList):
                        wList.append(l)
                        inList.add(l)

    return state

LiveVarsState = Set[str]
def livevars(fun: Function) -> DFlowStateT[LiveVarsState]:
    """ Compute live variables at each program location using
        backwards dataflow analysis
    """
    transformer_m = {
        AstAssert:  lambda stmt, inS: inS.union(stmt_read(stmt)),
        AstAssume:  lambda stmt, inS: inS.union(stmt_read(stmt)),
        AstHavoc:  lambda stmt, inS: inS - stmt_changed(stmt),
        AstAssignment:  lambda stmt, inS:   \
            (inS - stmt_changed(stmt)).union(stmt_read(stmt))
    }

    return dataflow(fun, transformer_m, lambda a,b: a.union(b), set(), set([v[0] for v in fun.returns]), False)

PredicateSetT = Optional[Set[AstExpr]]
def propagateUnmodifiedPreds(fun: Function) -> DFlowStateT[PredicateSetT]:
    """ Propagate predicates through the function, as long as we can
        syntactically tell they still hold. This requires checking that any of
        the variables they use are not overwritten, since the location where they
        are defined. Our predicates come from 3 sources:
            1) Function pre-conditions
            2) assume statements (e.g. assume (x>0) produces x>0)
            3) assignments (e.g. x:= y+1 produces x == y+1)
    """
    def assignment_preds(stmt: AstAssignment) -> Set[AstExpr]:
      """ Compute predicate x = expr from assignment x:=expr if x is not in expr """
      assert isinstance(stmt.lhs, AstId) # m[X] := ..; re-writen to m = update(m, x, ...)
      return set([AstBinExpr(stmt.lhs, "==", stmt.rhs)]) \
        if str(stmt.lhs) not in expr_read(stmt.rhs) else set()

    def filterModifiedPreds(preds: PredicateSetT, stmt: AstStmt) -> Set[AstExpr]: 
      """ Remove predicates using any of the clobbered_vars """
      clobbered_vars: Set[str] = stmt_changed(stmt)
      assert preds is not None
      return set([x for x in preds \
                    if len(clobbered_vars.intersection(expr_read(x))) == 0])

    transformer_m = {
        AstAssert:  lambda stmt, inS: inS,
        AstAssume:  lambda stmt, inS: inS.union(set([stmt.expr])),
        AstHavoc:  lambda stmt, inS: filterModifiedPreds(inS, stmt),
        AstAssignment:  lambda stmt, inS:
            filterModifiedPreds(inS, stmt).union(assignment_preds(stmt))
    }

    def unionF(a: PredicateSetT, b: PredicateSetT) -> PredicateSetT:
        if (a is None): return b
        if (b is None): return a

        return a.intersection(b)

    # TODO: Once support for procedures with bodies is added, (and thus pre/post conditions added to Function class)
    # modify start set to include function precondition
    return dataflow(fun, transformer_m, unionF, None, set(), True)