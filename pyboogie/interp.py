from .bb import BB, Function
from copy import copy
from .util import unique, ccast
from .ast import AstAssert, AstAssume, AstHavoc, AstAssignment, AstGoto, \
  AstReturn, AstUnExpr, AstBinExpr, AstNumber, AstId, AstTrue, AstFalse, \
  AstExpr, AstMapIndex, ast_and, AstForallExpr, AstBinding, AstIntType, ReplMap_T, \
  AstMapUpdate
from typing import Any, Dict, Callable, Union, Iterable, Tuple, Set, List, NamedTuple, Optional
from .ssa import SSAEnv
from .ssa import SSAEnv, is_ssa_str, unssa_str
from frozendict import frozendict
from typing import Any, Dict, Callable, Union, Iterable, Tuple, Set, List, NamedTuple, Optional
from pyparsing import Forward, nums, Word, ParserElement, ParseResults, delimitedList as csl, StringEnd,\
  Optional as O,\
  Literal as L,\
  Group as G, \
  Suppress as S
import re

class BoogieMap:
    def __init__(self, explicit_cases: Dict["BoogieVal", "BoogieVal"], default: Optional["BoogieVal"]=None) -> None:
      self._explicit_cases = explicit_cases
      self._default_case = default

    def __hash__(self) -> int:
      return hash((tuple(sorted(self._explicit_cases.items())), self._default_case))

    @staticmethod
    def to_dict(f: "BoogieMap") -> Dict[Any, Any]:
      return { "default": f._default_case, "explicit": f._explicit_cases }

    @staticmethod
    def from_dict(d: Dict[Any, Any]) -> "BoogieMap":
      return BoogieMap(d["explicit"], d["default"])

    def lookup(self, key: "BoogieVal") -> "BoogieVal":
      if key in self._explicit_cases:
        return self._explicit_cases[key]
      else:
        return self._default_case

    def mapUpdate(self, val: "BoogieMap", key: "BoogieVal", newVal: "BoogieVal"):
      if key in val._explicit_cases:
        if newVal == val._default_case:
          del val._explicit_cases[key]
        else:
          self._explicit_cases[key] = newVal
      else:
        self._explicit_cases.update({key: newVal})
      return BoogieMap(val._explicit_cases, val._default_case)

    def __eq__(self, other: object) -> bool:
      if not isinstance(other, BoogieMap):
        return False
      return self._explicit_cases == other._explicit_cases and self._default_case == other._default_case 

    def __str__(self):
      s = "{"
      s += ",".join([str(k) + ":" + str(v) for (k,v) in self._explicit_cases.items()])
      if self._default_case is not None:
        s += "|" + str(self._default_case)
      s += "}"
      return s

class BoogieValParser:
  def __init__(self) -> None:
    BoogieInt: ParserElement["BoogieVal"] = O("-") + Word(nums)

    def parseInt(s: str, loc: int, toks: "ParseResults[Any]") -> List["BoogieVal"]:
      return [int("".join(toks))]
    BoogieInt.setParseAction(parseInt)

    BoogieBool: ParserElement["BoogieVal"] = L("True") | L("False")

    def parseBool(s: str, loc: int, toks: "ParseResults[Any]") -> List["BoogieVal"]:
      return [toks[0]=="True"]
    BoogieBool.setParseAction(parseBool)

    BoogieMapRule: Forward = Forward()
    BoogieValRule: ParserElement["BoogieVal"] = BoogieInt | BoogieBool | BoogieMapRule
    BoogieMapRule << (S(L("{")) + G(csl(G(BoogieValRule + S(L(":")) + BoogieValRule))) +\
                                    O(S(L("|")) + BoogieValRule) + S(L("}")))

    def parseMap(s: str, loc: int, toks: "ParseResults[Any]") -> List[BoogieVal]:
      print(toks)
      explicitVals : Dict["BoogieVal", "BoogieVal"] = {key: val for (key,val) in toks[0]}
      defaultVal: Optional["BoogieVal"] = None
      if (len(toks) == 2):
        defaultVal = toks[1]
      return [BoogieMap(explicitVals, defaultVal)]

    BoogieMapRule.setParseAction(parseMap)
    self._root = BoogieValRule

  def parse(self, s: str) -> "BoogieVal":
    return self._root.parseString(s)[0]
 

class OpaqueVal(object):
    @staticmethod
    def to_dict(f: "OpaqueVal") -> Dict[Any, Any]:
      return {  }

    @staticmethod
    def from_dict(d: Dict[Any, Any]) -> "OpaqueVal":
      return OpaqueVal()

#TODO(shraddha): After arrays are implemented, think about whether OpaqueVal is still neccessary. This may
# require looking at the KRML document, to try and see what other concrete data-types and values exist in Boogie?
BoogieVal = Union[int, bool, BoogieMap, OpaqueVal]
Store = Dict[str, BoogieVal]
PC = NamedTuple("PC", [("bb", BB), ("next_stmt", int)])
State = NamedTuple("State", [("pc", PC), ("store", Store), ("status", str)])
Trace = List[State]
States = Set[State]

RandF = Callable[[State, str], BoogieVal]
ChoiceF = Callable[[Iterable[State]], List[State]]

def val_to_ast(v: BoogieVal) -> AstExpr:
  if isinstance(v, int):
    return AstNumber(v)
  elif isinstance(v, bool):
    return AstTrue() if v else AstFalse()
  else:
    assert False, "Can't convert {} to ast node".format(v)

keyfactory = SSAEnv()

def map_to_expr(val: BoogieMap, ex: AstExpr) -> AstExpr:
	"""Given a Boogie map 'val' and an AstExpr 'ex' return a Boogie expression equivalent to ex contains val
	For example: val is {5->6, _->0} and ex is a[3] then map_to_expr returns

	a[3][5] == 6 && forall j: int :: (j != 5) ==> a[3][j] == 0
	"""
	exprs : List[AstExpr] = []

	for(fromV, toV) in val._explicit_cases.items():
		arr_index = AstMapIndex(ex, val_to_ast(fromV))

		if(isinstance(toV,int)):
			exprs.append(AstBinExpr(arr_index, "==", val_to_ast(toV)))
		else:
			exprs.append(map_to_expr(toV, arr_index))

	if val._default_case is not None:
		keyname = keyfactory.lookup("_key_")
		keyfactory.update("_key_")
		key = AstId(keyname)
		new_ex = AstMapIndex(ex,key)
		not_explicit = ast_and([AstBinExpr(key, "!=", val_to_ast(x)) for x in val._explicit_cases.keys()])

		if (isinstance(val._default_case, int)):
			anticedent : AstExpr = AstBinExpr(new_ex, "==", val_to_ast(val._default_case))
		else:
			anticedent = map_to_expr(val._default_case, new_ex)

		implication = AstForallExpr((AstBinding(("_key_",), AstIntType()),),
                                     AstBinExpr(not_explicit, "==>", anticedent))

		exprs.append(implication)

	return ast_and(exprs)

#TODO(Shraddha) : Consider the bool case

def store_to_expr(s: Store, suff:str ="") -> AstExpr:
    exprs : List[AstExpr] = []
    for (var, val) in s.items():
      if isinstance(val, BoogieMap):
			      exprs.append(map_to_expr(val, AstId(var + suff)))
      else:
			      exprs.append(AstBinExpr(AstId(var + suff), "==", val_to_ast(val)))

    return ast_and(exprs)

# Possible statuses:
STALLED="STALLED"   # reached an assume that is false
FAILED="FAILED"     # reached an assert that is false
FINISHED="FINISHED" # reached end of program
RUNNING="RUNNING"   # can still make progress

_logical_un = {
  '!':  lambda x: not x,
} #type: Dict[str, Callable[[bool], bool]]

_arith_un = {
  '-':  lambda x: -x,
} #type: Dict[str, Callable[[int], int]]


_logical_bin = {
  "&&": lambda x, y:  x and y,
  "||": lambda x, y:  x or y,
  "==>": lambda x, y:  (not x) or y,
} #type: Dict[str, Callable[[bool, bool], bool]]


_arith_bin = {
  "+": lambda x, y:  x + y,
  "-": lambda x, y:  x - y,
  "*": lambda x, y:  x * y,
  "div": lambda x, y:  x // y,
  "mod": lambda x, y:  x % y,
} #type: Dict[str, Callable[[int, int], int]]

_relational_bin = {
  "==": lambda x, y:  x == y,
  "!=": lambda x, y:  x != y,
  "<": lambda x, y:  x < y,
  ">": lambda x, y:  x > y,
  "<=": lambda x, y:  x <= y,
  ">=": lambda x, y:  x >= y,
} #type: Dict[str, Callable[[int, int], bool]]

class BoogieRuntimeExc(Exception):  pass

# TODO(shraddha): This needs to be update 2 new expressions: 
#  1) indexing expressions - e.g. arr[x]
#  2) map update expressions - e.g. arr[x:=5]. The expression arr[x:=5] means a new map, that is the same
# as the arr map, except for at the index corresponding to the value of x, it maps to 5.
def eval_quick(expr: AstExpr, store: Store) -> BoogieVal:
  """
  Evaluate an expression in a given environment. Boogie expressions are always
  pure so we don't modify the store. Raise a runtime error on:
    - type mismatch
    - lookup of free id
    - div by 0
  """
  if isinstance(expr, AstNumber):
    return expr.num
  elif isinstance(expr, AstTrue):
    return True
  elif isinstance(expr, AstFalse):
    return False
  elif isinstance(expr, AstId):
    try:
      return store[expr.name]
    except KeyError:
      raise BoogieRuntimeExc("Unknown id {}".format(expr.name))
  elif isinstance(expr, AstUnExpr):
    inner = eval_quick(expr.expr, store)
    op = expr.op

    if (op in _logical_un):
      assert isinstance(inner, bool)
      return _logical_un[op](inner)
    
    if (op in _arith_un):
      assert isinstance(inner, int)
      return _arith_un[op](inner)

    assert False, "Unknown unary op {}".format(op)
  elif isinstance(expr, AstBinExpr):
    lhs, rhs = (eval_quick(expr.lhs, store), eval_quick(expr.rhs, store))
    op = expr.op

    if (op in _logical_bin):
      assert isinstance(lhs, bool)
      assert isinstance(rhs, bool)
      return _logical_bin[op](lhs, rhs)
    
    if (op in _arith_bin):
      assert isinstance(lhs, int)
      assert isinstance(rhs, int)

      if (op == 'div' and rhs == 0):
        raise BoogieRuntimeExc("Divide by 0")

      return _arith_bin[op](lhs, rhs)

    if (op in _relational_bin):
      assert isinstance(lhs, int)
      assert isinstance(rhs, int)

      return _relational_bin[op](lhs, rhs)
    assert False, "Unknown binary op {}".format(op)

    if isinstance(expr, AstMapIndex):
      boogieMap : BoogieMap = ccast(eval_quick(expr.map, store), BoogieMap)
      index : BoogieVal = eval_quick(expr.index, store)

      return boogieMap.lookup(index)

    if isinstance(expr, AstMapUpdate):
      uboogieMap : BoogieMap = ccast(eval_quick(expr.map, store), BoogieMap)
      uindex : BoogieVal = eval_quick(expr.index, store)
      newVal : BoogieVal = eval_quick(expr.newVal, store)
      newMap = uboogieMap.mapUpdate(uboogieMap, uindex, newVal)

      return newMap

  else:
    assert False, "Unknown expression {}".format(expr)


def stalled(s):
  # type: (State) -> bool
  """
  Return true iff this state has stalled (reached unsatisfiable assume)
  """
  return s.status == STALLED


def active(s):
  # type: (State) -> bool
  """
  Return true iff this state can make progress
  """
  return s.status == RUNNING

def finished(s):
  # type: (State) -> bool
  """
  Return true iff this state is in the finished state
  """
  return s.status == FINISHED


def interp_one(state: State, rand: RandF) -> Iterable[State]:
  """
  Given a program bbs and a current state, return the set of possible next
  states
  """
  if not active(state):
    # Never escape a failed/stalled/finished state
    yield state
    return

  ((bb, next_stmt), store, status) = state
  assert 0 <= next_stmt and next_stmt <= len(bb)

  if next_stmt == len(bb):
    # At end of BB - any successor is fair game
    for s in bb.successors():
      yield State(PC(s, 0), copy(store), status)

    # If no successors we are at the end of the funciton. Yield a finished
    # state
    if (len(bb._successors) == 0):
      yield State(PC(bb, next_stmt + 1), store, FINISHED)
    return
  else:
    # Inside of a BB - interp the next statment
    stmt = bb[next_stmt]

    if isinstance(stmt, AstAssert):
      v = eval_quick(stmt.expr, store)
      assert isinstance(v, bool)
      if (not v):
        status = FAILED
    elif isinstance(stmt, AstAssume):
      v = eval_quick(stmt.expr, store)
      if (not v):
        status = STALLED
    elif isinstance(stmt, AstHavoc):
      store = copy(store)
      for var_id in stmt.ids:
        store[var_id.name] = rand(state, var_id.name)
    elif isinstance(stmt, AstAssignment):
      v = eval_quick(stmt.rhs, store)
      store = copy(store)
      store[ccast(stmt.lhs, AstId).name] = v
    else:
      assert False, "Can't handle statement {}".format(stmt)

    yield State(PC(bb, next_stmt + 1), store, status)

def unssa_z3_model(m: Store, repl_m: ReplMap_T) -> Store:
    updated = list(map(str, iter(repl_m.keys())))
    original = [ x for x in m.keys() if not is_ssa_str(x) and x not in updated ]
    res = { (unssa_str(x) if is_ssa_str(x) else x) : m.get(x, None)
                for x in original + list(map(str, iter(repl_m.values())))
          }
    return frozendict(res)

def trace_n(state: State, nsteps: int, rand: RandF, filt: ChoiceF)-> Tuple[List[Trace], List[Trace]]:
  """
  Given a program bbs and a current state state, and number of steps nsteps
  interpret the program for up to nsteps. Return two lists - the active traces
  (traces of length nsteps that can still make progress) and inactive traces
  (traces of length <=nsteps that are finished or failed).

    :param bbs: the basic blocks of the program to interpret
    :param state: the starting state of the program
    :param nsteps:  number of steps up to which to interpret
    :param rand:  a callback with signature (State, str) -> Value for providing
                  random values to havoc
    :param filt:  callback (Program, List[States])->List[States] called when we have multiple
                  possible next states. Allows the consumer to prune the non-determinism or change
                  exploration order.

    :return:  tuple (active_traces, inactive_traces).
              active_traces - a list of traces of length nsteps that can make
                              further progress
              inative_traces - a list of traces of length UP TO nsteps that are
                               either failed or finished.
  """
  active_traces = [ [state] ] # type: List[Trace]
  inactive_traces = [] # type: List[Trace]

  for step in range(nsteps):
    new_traces = [ ] # type: List[Trace]

    for t in active_traces:
      new_states = list(interp_one(t[-1], rand)) # type: List[State]
      # Don't care about stalled traces
      new_states = [x for x in new_states if not(stalled(x))]
      if (len(new_states) > 1):
        # If execution is non-deterministic here, allow consumer to prune the list
        # of next states
        new_states = filt(new_states)

      for st in new_states:
        new_traces.append(t + [ st ])
    
    # active_traces are just the traces of length step  
    active_traces = [t for t in new_traces if active(t[-1])]
    # inactive_traces are all FAILED/FINISHED traces of length <= step 
    inactive_traces.extend([t for t in new_traces if not active(t[-1])])

  return (active_traces, inactive_traces)

def trace_n_from_start(fun: Function, starting_store: Store, nsteps: int, rand: RandF, filt: ChoiceF) -> Tuple[List[Trace], List[Trace]]:
  starting_state = State(PC(fun.entry(), 0), starting_store, RUNNING)
  return trace_n(starting_state, nsteps, rand, filt)

if __name__ == "__main__":
  from argparse import ArgumentParser
  from .util import error
  from random import randint, choice

  p = ArgumentParser(description="interpeter")
  p.add_argument("file", type=str, help="path to desugared boogie file to interpret")
  p.add_argument("starting_env", type=str,
    help="comma separated list of starting assignments to variables." +
         "e.g. a=4,b=10,x=0")
  p.add_argument("steps", type=int, help="the number of steps for which to interpret")
  p.add_argument("--nond-mode", type=str,
    help="mode controlling what to do when execution is non-deterministic. " + 
         "Possible values:\n" +
            " all - explore all branches of the execution tree\n" +
            " random_lookahead_1 - remove all states that will stall after 1 step " +
            "and pick a random one from the rest",
    choices=["all", "random_lookahead_1"], default="all")

  args = p.parse_args()

  fun = unique(Function.load(args.file)) # type: Function
  # TODO(shraddha): This needs to be updated to support booleans and 
  # arrays. You may want to write a pair of generic functions:
  #
  # toStr(b: BoogieVal) -> str
  # fromStr(s: str) -> BoogieVal
  #
  # Note that toStr/fromStr for AstNumber and AstTrue/AstFalse are already written for you (basically .pp() and parseExprAst).
  # You just need to handle the case for maps.
  starting_store = {  k : v for (k, v) in
    [ x.split("=") for x in args.starting_env.split(".") ]
  } # type: Store

  if (args.nond_mode == "all"):
    filt_f = lambda states:  list(states) # type: ChoiceF
  elif (args.nond_mode == "random_lookahead_1"):
    def f(states: Iterable[State]) -> List[State]:
      def lookahead_one_filter(s: State) -> bool:
        if s.pc.next_stmt == len(s.pc.bb):
          return True

        stmt = s.pc.bb[s.pc.next_stmt]
        if not isinstance(stmt, AstAssume):
          return True

        v = eval_quick(stmt.expr, s.store)
        assert isinstance(v, bool)
        return v

      feasible_states = [x for x in states if lookahead_one_filter(x)]
      return [choice(feasible_states)]
    filt_f = f
  else:
    error("Usage: unknown nond-mode: {}".format(args.nond_mode))

  rand_f = lambda state, Id:  randint(-1000, 1000) # type: RandF

  starting_state = State(PC(fun.entry(), 0), starting_store, RUNNING)
  (active_ts, inactive_ts) = trace_n(starting_state, args.steps, rand_f, filt_f)

  def pp_state(st: State) -> str:
    return "[{},{}]: ".format(st.pc.bb, st.pc.next_stmt) + \
           ",".join([k + "={}".format(v) for (k, v) in st.store.items()])

  def pp_trace(t: Trace) -> str:
    return "->\n".join(map(pp_state, t))


  print("Active({}):".format(len(active_ts)))
  for t in active_ts:
    print(pp_trace(t))
  print("Inactive({}):".format(len(inactive_ts)))
  for t in inactive_ts:
    print(pp_trace(t))
