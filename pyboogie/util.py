from typing import Any, TypeVar, Iterable, Callable, Set, Union, List, Tuple, Sized, Dict, Type
import traceback
from itertools import chain, combinations
from sys import exc_info, stderr
from random import choice
from functools import reduce

T = TypeVar("T")
TSized = TypeVar("TSized", bound=Sized)
SizedIterable=Union[List[T], Set[T]]

C = TypeVar("C", bound=object)
def ccast(a: Any, t: Type[C]) -> C:
    """ Checked cast down to the type t """
    assert isinstance(a, t), "Expected an instance of {} but got {}".format(t, a)
    return a

def clcast(a: Any, t: Type[C]) -> List[C]:
    """ Checked cast down to the type List[t] """
    return [ccast(x, t) for x in a]

def error(*args: Any) -> None:
  if (len(args) > 0 and str(args[0]) and '%' in args[0]):
    fmt = args[0]
    rest = args[1:]
    if '\n' not in fmt:
        fmt += '\n'
    stderr.write(fmt % tuple(rest))
  else:
    stderr.write(" ".join(map(str, args)) + "\n")

def fatal(*args: Any) -> None:
  error(*args)
  exit(-1)

def unique(iterable: Iterable[T], msg: str ="") -> T:
  """ assert that iterable has one element and return it """
  l = list(iterable)
  assert len(l) == 1, msg
  return l[0]

def powerset(s: SizedIterable) -> Iterable[Set[T]]:
  """ Return the powerset of a set s """
  it = chain.from_iterable(combinations(s, l) for l in range(len(s) + 1))
  for subS in it:
    yield set(subS)

def split(pred: Callable[[T], bool], itr: Iterable[T]) -> Tuple[Iterable[T], Iterable[T]]:
    """ Split a list based on a predicate function """
    yes,no = [], []
    for i in itr:
        if (pred(i)):
            yes.append(i);
        else:
            no.append(i);

    return (yes, no)

def nonempty(lst: Iterable[TSized]) -> List[TSized]:
    """ Filter out the empty elements of a list (where empty is len(x) == 0)
    """
    return [x for x in lst if len(x) > 0]

def flattenList(s: Iterable[List[T]]) -> List[T]:
  return reduce(lambda x,y: x + y, s, [])

def first(it: Iterable[T], pred: Callable[[T], bool]) -> int:
    ctr = 0
    for v in it:
        if pred(v):
            return ctr
        ctr += 1
    return -1


_uids = {}  # type: Dict[str,int]


def get_uid(prefix: str) -> str:
    global _uids

    if prefix not in _uids:
        _uids[prefix] = -1

    _uids[prefix] += 1

    return prefix + "_" + str(_uids[prefix])


def ite(c: bool, a: T, b: T) -> T:
    return a if c else b
