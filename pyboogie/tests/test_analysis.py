""" 
Tests for implemented analyses
"""
from unittest import TestCase
from typing import Any, List, Tuple
from ..ast import parseAst, parseExprAst
from ..bb import Function
from ..analysis import livevars, propagateUnmodifiedPreds, PredicateSetT, LiveVarsState, DFlowStateT
from functools import reduce

class TestAnalysis(TestCase):
    testLivenessProgs : List[Tuple[str, Any]] = [
        ("""implementation main() {
         }""",
        { ("__dummy_exit__", 0): set()}),
        ("""implementation main() {
            var x: int;
         }""",
        { ("__dummy_exit__", 0): set()}),
        ("""implementation main() {
            var x: int;
            start: x := 1;
         }""",
        { ("start", 0): set(),
          ("start", 1): set()
        }),
        ("""implementation main() {
            var x, y: int;
            start: x := y;
         }""",
        { ("start", 0): set("y"),
          ("start", 1): set(),
        }),
        ("""implementation main() {
            var x, y,z: int;
            start:
                x := y;
                x := y+1;
                y := z;
         }""",
        { ("start", 0): set(["y", "z"]),
          ("start", 1): set(["y", "z"]),
          ("start", 2): set("z"),
          ("start", 3): set(),
        }),
        ("""implementation main() {
            var i: int;
            start:
                goto then, else;
            then:
                goto exit;
            else:
                assert (i>0);
                goto exit;
            exit:
         }""",
        { ("start", 0): set(["i"]),
          ("else", 0): set(["i"]),
          ("else", 1): set([]),
          ("then", 0): set([]),
          ("exit", 0): set(),
        }),
        ("""implementation main() {
            var n, i: int;
            start:
                assume n>0;
                i := 0;
                goto hdr;
            hdr:
                goto body, exit;
            body:
                assume (i<n);
                i := i + 1;
                goto hdr;
            exit:
         }""",
        { ("start", 0): set(["n"]),
          ("start", 1): set(["n"]),
          ("hdr", 0): set(["n", "i"]),
          ("body", 0): set(["n", "i"]),
          ("body", 1): set(["n", "i"]),
          ("exit", 0): set(),
        }),
    ]

    def testLiveness(self):
        """ 
        """
        for (text, expected) in self.testLivenessProgs:
            prog = parseAst(text) # type: AstProgram
            assert(len(prog.decls) == 1)
            fun = Function.build(prog.decls[0])
            res = livevars(fun)
            for ((bbLbl, idx), val) in expected.items():
                bb = fun.get_bb(bbLbl)
                assert res[(bb, idx)]== expected[(bbLbl, idx)], "Got {} expeced {} at location {} in {}"\
                    .format(res[(bb, idx)], expected[(bbLbl, idx)], (bbLbl, idx), fun.pp())

    testPropagatePredsProgs : List[Tuple[str, Any]] = [
        ("""implementation main() {
         }""",
        { ("__dummy_exit__", 0): set()}),
        ("""implementation main() {
            var x: int;
         }""",
        { ("__dummy_exit__", 0): set()}),
        ("""implementation main() {
            var x: int;
            start: x := 1;
         }""",
        { ("start", 0): set(),
          ("start", 1): set(["x==1"])
        }),
        ("""implementation main() {
            var x, y: int;
            start: x := y;
         }""",
        { ("start", 0): set(),
          ("start", 1): set(["x==y"]),
        }),
        ("""implementation main() {
            var x, y,z: int;
            start:
                x := y;
                x := y+1;
                y := z;
         }""",
        { ("start", 0): set(),
          ("start", 1): set(["x==y"]),
          ("start", 2): set(["x==y+1"]),
          ("start", 3): set(["y==z"]),
        }),
        ("""implementation main() {
            var i: int;
            start:
                goto then, else;
            then:
                goto exit;
            else:
                assert (i>0);
                goto exit;
            exit:
         }""",
        { ("start", 0): set(),
          ("else", 0): set(),
          ("else", 1): set([]),
          ("then", 0): set(),
          ("exit", 0): set(),
        }),
        ("""implementation main() {
            var n, i: int;
            start:
                assume n>0;
                i := 0;
                goto hdr;
            hdr:
                goto body, exit;
            body:
                assume (i<n);
                i := i + 1;
                goto hdr;
            exit:
         }""",
        { ("start", 0): set(),
          ("start", 1): set(["n>0"]),
          ("start", 2): set(["n>0", "i==0"]),
          ("hdr", 0): set(["n>0"]),
          ("body", 0): set(["n>0"]),
          ("body", 1): set(["n>0", "i<n"]),
          ("exit", 0): set(["n>0"]),
        }),
        ("""implementation main() {
            var n, i: int;
            start:
                assume n>0;
                i := 0;
                goto hdr;
            hdr:
                goto body, exit;
            body:
                assume (i<n);
                i := i + 1;
                goto hdr;
            exit:
                assume (i>=n);
         }""",
        { ("start", 0): set(),
          ("start", 1): set(["n>0"]),
          ("start", 2): set(["n>0", "i==0"]),
          ("hdr", 0): set(["n>0"]),
          ("body", 0): set(["n>0"]),
          ("body", 1): set(["n>0", "i<n"]),
          ("exit", 0): set(["n>0"]),
          ("exit", 1): set(["i>=n", "n>0"]),
        }),
    ]

    def testPropagateUnmodifiedPreds(self):
        """ 
        """
        for (text, expected) in self.testPropagatePredsProgs:
            prog : AstProgram = parseAst(text)
            assert(len(prog.decls) == 1)
            fun = Function.build(prog.decls[0])
            res = propagateUnmodifiedPreds(fun)
            for ((bbLbl, idx), val) in expected.items():
                bb = fun.get_bb(bbLbl)
                assert res[(bb, idx)]== set(map(parseExprAst, expected[(bbLbl, idx)])), "Got {} expeced {} at location {} in {}"\
                    .format(res[(bb, idx)], expected[(bbLbl, idx)], (bbLbl, idx), fun.pp())