from unittest import TestCase
from ..grammar import BoogieParser
from ..ast import parseAst, parseExprAst, AstProgram, AstImplementation, AstBody

class TestAst(TestCase):
    def test_simple(self):
        prog = "implementation main() {}"
        node = parseAst(prog)
        expected = AstProgram([AstImplementation("main", ([], []), AstBody([], []))])
        assert (node == expected), "Expected: {} got {}".format(str(node), str(expected))