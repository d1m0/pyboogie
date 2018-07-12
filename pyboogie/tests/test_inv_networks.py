""" 
Tests for verification routines in invariant_networks.py
"""
from unittest import TestCase
from typing import Any, List, Tuple, Dict
from ..ast import parseAst, parseExprAst
from ..bb import Function
from ..inv_networks import checkInvNetwork, filterCandidateInvariants
from functools import reduce
from ..util import ccast
from ..paths import SSABBNode

ViolationPattern = Tuple[str, List[str]]

class TestInvariantNetworks(TestCase):
    testCases: List[Tuple[str, str, str, List[Tuple[Dict[str, List[str]], List[ViolationPattern], Dict[str, List[str]]]]]] = [
        ("""implementation main() {
         }""",
         "true",
         "true",
         [({}, [], {"__dummy_exit__": ["true"]})]),
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
            ({"hdr": ["true"]}, [("safety", ['hdr', 'exit'])], {"hdr": ["true"], "start": ["true"]}),
            ({"hdr": ["false"]}, [("inductiveness", ['start', 'hdr'])], {"hdr": [], "start": ["true"]}),
            ({"hdr": ["i==0"]}, [("inductiveness", ['hdr', 'body', 'hdr']), 
                                 ("safety", ['hdr', 'exit'])], {"hdr": [], "start": ["true"]}),
            ({"hdr": ["i<1"]}, [("inductiveness", ['hdr', 'body', 'hdr']), 
                                 ("safety", ['hdr', 'exit'])], {"hdr": [], "start": ["true"]}),
            ({"hdr": ["i<=n"]}, [], {"hdr": ["(i <= n)"], "start":["true"]}),
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
            ({"hdr": ["true"]}, [("safety", ['hdr', 'exit'])], {"hdr": ["true"], "start": ["true"]}),
            ({"hdr": ["false"]}, [("inductiveness", ['start', 'hdr'])], {"hdr": [], "start": ["true"]}),
            ({"hdr": ["x==y"]}, [("inductiveness", ['hdr', 'body', 'hdr'])], {"hdr": [], "start": ["true"]}),
            ({"hdr": ["z==w"]}, [("safety", ['hdr', 'exit'])], {"hdr": ["(z == w)"], "start": ["true"]}),
            ({"hdr": ["x==y", "z==w"]}, [], {"hdr": ["(x == y)", "(z == w)"], "start": ["true"]}),
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
            for (invs, expectedViolations, _) in veriCases:
                cutpoints = { lbl: list(map(parseExprAst, exprs)) for (lbl, exprs) in invs.items() }
                violations = checkInvNetwork(fun, pre, post, cutpoints, 10)

                simplifiedViolations = [(v._typ, [ccast(node, SSABBNode).bb.label for node in v._path]) for v in violations]
                simplifiedViolations.sort()
                assert simplifiedViolations == expectedViolations, "Expected violations {} instead got {} for invariants {}".format(expectedViolations, simplifiedViolations, invs)

    def testFilterInvNetwork(self):
        """ 
        """
        for (progText, precond, postcond, veriCases) in self.testCases:
            prog: AstProgram = parseAst(progText)
            fun: Function = Function.build(prog.decls[0])
            pre: AstExpr = parseExprAst(precond)
            post: AstExpr = parseExprAst(postcond)
            for (invs, _, expectedSoundInvs) in veriCases:
                cutpoints = { lbl: list(map(parseExprAst, exprs)) for (lbl, exprs) in invs.items() }
                (overfitted, nonind, sound, violations) = filterCandidateInvariants(fun, pre, post, cutpoints, 10)

                strSound = {hdr: sorted(list(map(str, invs))) for (hdr,invs) in sound.items()}
                assert strSound == expectedSoundInvs, "Expected remaining strSound invs {} instead got {} for invariants {}".format(expectedSoundInvs, strSound, invs)