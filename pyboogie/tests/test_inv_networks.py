""" 
Tests for verification routines in invariant_networks.py
"""
from unittest import TestCase
from typing import Any, List, Tuple, Dict
from ..ast import parseAst, parseExprAst
from ..bb import Function
from ..inv_networks import checkInvNetwork
from functools import reduce
from ..util import ccast
from ..paths import SSABBNode

ViolationPattern = Tuple[str, List[str]]

class TestInvariantNetworks(TestCase):
    testCases: List[Tuple[str, str, str, List[Tuple[Dict[str, List[str]], List[ViolationPattern]]]]] = [
        ("""implementation main() {
         }""",
         "true",
         "true",
         [({}, [])]),
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
                assume(i >= n);
                assert(i == n);
         }""",
         "true",
         "true",
         [
            ({"hdr": ["true"]}, [("safety", ['hdr', 'exit'])]),
            ({"hdr": ["false"]}, [("inductiveness", ['start', 'hdr'])]),
            ({"hdr": ["i==0"]}, [("inductiveness", ['hdr', 'body', 'hdr']), 
                                 ("safety", ['hdr', 'exit'])]),
            ({"hdr": ["i<1"]}, [("inductiveness", ['hdr', 'body', 'hdr']), 
                                 ("safety", ['hdr', 'exit'])]),
            ({"hdr": ["i<=n"]}, []),
         ]),
        ("""implementation main() {
            var x, y, z, w: int;
            start:
                assume (x == y && z == w);
                goto hdr;
            hdr:
                goto body, exit;
            body:
                x:= x + z;
                y:= y + w;
                goto hdr;
            exit:
                assert(x == y);
         }""",
         "true",
         "true",
         [
            ({"hdr": ["true"]}, [("safety", ['hdr', 'exit'])]),
            ({"hdr": ["false"]}, [("inductiveness", ['start', 'hdr'])]),
            ({"hdr": ["x==y"]}, [("inductiveness", ['hdr', 'body', 'hdr'])]),
            ({"hdr": ["z==w"]}, [("safety", ['hdr', 'exit'])]),
            ({"hdr": ["x==y", "z==w"]}, []),
         ]),
    ]

    def testCheckInvNetwork(self):
        """ 
        """
        for (progText, precond, postcond, veriCases) in self.testCases:
            prog: AstProgram = parseAst(progText)
            fun: Function = Function.build(prog.decls[0])
            pre: AstExpr = parseExprAst(precond)
            post: AstExpr = parseExprAst(postcond)
            for (invs, expectedViolations) in veriCases:
                cutpoints = { lbl: list(map(parseExprAst, exprs)) for (lbl, exprs) in invs.items() }
                violations = checkInvNetwork(fun, pre, post, cutpoints, 10)

                simplifiedViolations = [(v._typ, [ccast(node, SSABBNode).bb.label for node in v._path]) for v in violations]
                simplifiedViolations.sort()
                assert simplifiedViolations == expectedViolations, "Expected violations {} instead got {} for invariants {}".format(expectedViolations, simplifiedViolations, invs)