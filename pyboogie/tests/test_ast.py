from unittest import TestCase
from ..grammar import BoogieParser
from ..ast import parseAst, parseExprAst, AstProgram, AstImplementation,\
    AstBody, AstBinding, AstIntType, AstAssignment, AstId, AstBinExpr, AstNumber

class TestAst(TestCase):
    testProgs = [
        (
            """
                implementation main() {
                }
            """,
            AstProgram([AstImplementation("main", [], [], AstBody([], []))])
        ),
        (
            """
                implementation main() {
                    var x: int;
                }
            """,
            AstProgram([
                AstImplementation("main", [], [],
                    AstBody([AstBinding(["x"], AstIntType())], []))])
        ),
        (
            """
                implementation main() {
                    var x: int;
                    x := x+42;
                }
            """,
            AstProgram([
                AstImplementation("main", [], [],
                    AstBody([AstBinding(["x"], AstIntType())],
                    [AstAssignment(AstId('x'), AstBinExpr(AstId("x"), "+", AstNumber(42)))]))])
        ),

    ]
    def test_parse(self):
        """ For each pair of text S and expected parse tree T in
            TestAst.testProgs check parseAst(S) == T
        """
        for (text, expectedAst) in self.testProgs:
            root = parseAst(text)
            assert (root == expectedAst), "Expected: \n{} instead got \n{} from raw text \n{}"\
                .format(str(expectedAst), str(root), text)

    def test_roundtrip(self):
        "For each parse tree T in TestAst.testProgs check parseAst(str(T)) == T"
        for (_, expected) in self.testProgs:
            try:
                got = parseAst(str(expected))
                assert (expected == got), "Pretty-printed and parsed tree {} differs from original {}"\
                    .format(str(got), str(expected))
            except:
                print ("Failed parsing {}".format(str(expected)))
                raise