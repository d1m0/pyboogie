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
# For a BB 'A', and a state S: DFlowStateT, S['A', 0] described the state
# before the first instruction in 'A'. If 'A' has n instructions S['A', n-1]
# described the state before the last instruction in 'A' and S['A', n]
# describes the state after it - i.e. the state after 'A' completes.
DFlowStateT = Dict[LocT, StateT]

def dataflow(fun: Function, transformerMap: TransformerMapT, unionF: UnionT, bottom: StateT, forward: bool) -> DFlowStateT:
    # Start with all locations mapped to bottom
    state = { (bb, idx): copy(bottom) for bb in fun.bbs() for idx in range(len(bb))} # type: DFlowStateT

    # Compute the first entry on the worklist - entry or exit of CFG depending on forward argument
    if (forward):
        entryLoc = (fun.entry(), 0)
    else:
        exitBl = fun.exit()
        entryLoc = (exitBl, len(exitBl))
    wList = [ entryLoc ]

    nextLocsFunc = nextLocations if forward else prevLocations # type: Callable[[LocT], List[LocT]]

    while len(wList) > 0:
        curLoc = wList.pop()
        curBB, curIdx = curLoc
        inState = state[curLoc]
        outLabels = nextLocsFunc(curLoc)

        if ((curIdx == len(curBB) and forward) or
            (curIdx == 0 and not forward)):
            # Propagating new state across edges between BBs. No instruction is executed
            outState = inState
        else:
            # Propagating new state across an instruction inside a BB. Run the transformer function
            assert(len(outLabels) == 1)
            curStmt = curBB[curIdx]
            outState = transformerMap[curStmt.__class__](curStmt, inState)

        for l in outLabels:
            updatedOutState = unionF(state[l], outState)

            if (updatedOutState != state[l]):
                state[l] = updatedOutState 
                wList.append(l)

    return state

T=TypeVar("T")
Transformer_T = Dict[type, Callable[[AstStmt, Set[T]], Set[T]]]
Union_T = Callable[[Iterable[Set[T]]], Set[T]]
DFlowState_T = Dict[LabelT, Set[T]]

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
    } # type: TransformerMapT
    def union_f(a: LiveVarsState, b: LiveVarsState) -> LiveVarsState:
        return a.union(b)
    return dataflow(fun, transformer_m, union_f, set(), False)

PredicateSetT = Set[AstExpr]
def propagateUnmodifiedPreds(fun: Function) -> DFlowStateT[PredicateSetT]:
    """ Propagate assume and "==" predicates through the function, as long as
        any of the variables they use are not overwritten.
    """
    def assignment_preds(stmt: AstAssignment) -> PredicateSetT:
      """ Compute predicate x = expr from assignment x:=expr if x is not in expr """
      assert isinstance(stmt.lhs, AstId) # m[X] := ..; re-writen to m = update(m, x, ...)
      return set([AstBinExpr(stmt.lhs, "==", stmt.rhs)]) \
        if str(stmt.lhs) not in expr_read(stmt.rhs) else set()

    def filterModifiedPreds(preds: PredicateSetT, clobbered_vars: Set[str]) -> PredicateSetT: 
      """ Remove predicates using any of the clobbered_vars """
      return set([x for x in preds \
                    if len(clobbered_vars.intersection(expr_read(x))) == 0])

    transformer_m = {
        AstAssert:  lambda stmt, inS: inS,
        AstAssume:  lambda stmt, inS: inS.union(set([stmt.expr])),
        AstHavoc:  lambda stmt, inS: filterModifiedPreds(inS, stmt_changed(stmt)),
        AstAssignment:  lambda stmt, inS:
            filterModifiedPreds(inS, stmt_changed(stmt)).union(assignment_preds(stmt))
    }

    # TODO: Types seem weird here. Not clear why I need None. Needs TLC
    def union_f(a: PredicateSetT, b: PredicateSetT) -> PredicateSetT:
        return a.union(b)

    return dataflow(fun, transformer_m, union_f, set(), True)