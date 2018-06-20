""" 
Tests for basing Boogie parsing and AST building.
These tests focus on the core subset of boogie supported.
"""
from unittest import TestCase
from ..grammar import BoogieParser
from ..ast import parseAst, parseExprAst, AstProgram, AstImplementation,\
    AstBody, AstBinding, AstIntType, AstAssignment, AstId, AstBinExpr, AstNumber, replace,\
    AstMapIndex, AstMapUpdate, AstFuncExpr, AstMapType, AstBoolType, AstBVType, AstCompoundType,\
    parseType, AstTypeConstructorDecl, astBuilder, AstAttribute
from pyparsing import ParseException, StringEnd

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
                    AstBody([AstBinding(("x",), AstIntType())], []))])
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
                    AstBody([AstBinding(("x",), AstIntType())],
                    [AstAssignment(AstId('x'), AstBinExpr(AstId("x"), "+", AstNumber(42)))]))])
        ),

    ]
    def test_bad_parse(self):
        """ Make sure parseAst doesn't fail silently
        """
        badProgs = [
            "foo",
            "implementation main ()",
            "implementation main () {",
            "implementation main () returns () {}",
            """implementation main () returns () {
                a:= 1
            }""",
        ]
        for text in badProgs:
            with self.assertRaises(ParseException):
                parseAst("badProgs")

    def test_parse(self):
        """ For each pair of text S and expected parse tree T in
            TestAst.testProgs check parseAst(S) == T
        """
        for (text, expectedAst) in self.testProgs:
            root = parseAst(text)
            assert (root == expectedAst), "Expected: \n{} instead got \n{} from raw text \n{}"\
                .format(str(expectedAst), str(root), text)

    def testId(self):
        tests = [
            ("x", AstId("x")),
            ("x?.$_~+~$#~", AstBinExpr(AstId("x?.$_~"), "+", AstId("~$#~"))),
        ]
        for (text, expectedAst) in tests:
            try:
                ast = parseExprAst(text)
            except:
                print ("Failed parsing {}".format(text))
                raise
            assert (ast == expectedAst)

        
        badTests = [
            # Identifiers don't start with numbers
            ("4a"), ("4?.$_~+~$#~"),
            # Identifiers don't include bin operators
            ("x-"), ("x+"), ("x*"), ("x/"), ("x("), ("x)"), ("x%"),
        ]
        for text in badTests:
            with self.assertRaises(ParseException):
                parseExprAst(text)

    def testAtomParse(self):
        """ Test various atom parsings (especially mixing map update/index) """
        tests = [
            ("x", AstId("x")),
            ("x[4]", AstMapIndex(AstId("x"), AstNumber(4))),
            ("x[4][5]", AstMapIndex(AstMapIndex(AstId("x"), AstNumber(4)), AstNumber(5))),
            ("x[x:=5][4]", AstMapIndex(AstMapUpdate(AstId("x"), AstId("x"), AstNumber(5)), AstNumber(4))),
            ("x(1,2)[x:=5][4]", AstMapIndex(AstMapUpdate(AstFuncExpr("x", [AstNumber(1), AstNumber(2)]), AstId("x"), AstNumber(5)), AstNumber(4))),
        ]
        for (text, expectedAst) in tests:
            try:
                ast = parseExprAst(text)
            except:
                print ("Failed parsing {}".format(text))
                raise
            assert (ast == expectedAst)

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

    def test_replace(self):
        "Check that replace() function works correctly"
        tests = [
            ("x+y", {AstId('x'): AstNumber(42)}, "(42+y)"),
            ("x+y", {AstId('z'): AstNumber(42)}, "(x+y)"),
            ("x+(y+z)", {AstId('y'): AstNumber(42), parseExprAst('y+z'): AstNumber(43)}, "(x+43)"),
        ]
        for (expr, replM, expected) in tests:
            origExpr = parseExprAst(expr) if (isinstance(expr, str)) else expr
            replacedExp = replace(origExpr, replM)
            expectedExpr = parseExprAst(expected) if (isinstance(expected, str)) else expected
            assert (replacedExp == expectedExpr),\
                "Bad replace: Expected {} got {}".format(expected, replacedExp)

    def testTypes(self):
        good =[
            ("[int]int", AstMapType([], [AstIntType()], AstIntType())),
            ("[int, bool]int", AstMapType([], [AstIntType(), AstBoolType()], AstIntType())),
            ("<a>[a]a", AstMapType([("a")], [AstCompoundType(("a"), [])], AstCompoundType(("a"), []))),
            ("<a>[a]int", AstMapType([("a")], [AstCompoundType(("a"), [])], AstIntType())),
            ("C a", AstCompoundType(("C"), [AstCompoundType(("a"), [])])),
            ("<a>[C a, int]bool", AstMapType([("a")], [AstCompoundType(("C"), [AstCompoundType(("a"), [])]), AstIntType()], AstBoolType())),
            ("C a b c", AstCompoundType(("C"), [AstCompoundType(("a"), []), AstCompoundType(("b"), []), AstCompoundType(("c"), [])])),
            ("C a (b c)", AstCompoundType(("C"), [AstCompoundType(("a"), []), AstCompoundType(("b"), [AstCompoundType(("c"), [])])])),
            ("C a int c", AstCompoundType(("C"), [AstCompoundType(("a"), []), AstIntType(), AstCompoundType(("c"), [])])),
            ("C a (b int)", AstCompoundType(("C"), [AstCompoundType(("a"), []), AstCompoundType(("b"), [AstIntType()])])),
            ("C a [b]int", AstCompoundType(("C"), [AstCompoundType(("a"), []), AstMapType([], [AstCompoundType(("b"), [])], AstIntType())])),
            ("bv5", AstBVType(5)),
            ("C bv5 int", AstCompoundType(("C"), [AstBVType(5), AstIntType()]))
        ]

        bad = [
            ("C [int]int a"), # Map types must be the last type in type argument list
        ]
        for (text, expectedAst) in good:
            try:
                t = parseType(text)
            except ParseException:
                print("Failed parsing", text)
                raise
            assert t == expectedAst, "Expected: {} got {}".format(expectedAst, t)

        for text in bad:
            with self.assertRaises(ParseException):
                parseType(text)

    def testDecls(self):
        good =[
            ("type C;", AstTypeConstructorDecl("C", [], False, [])),
            ("type C A;", AstTypeConstructorDecl("C", ["A"], False, [])),
            ("type finite C A;", AstTypeConstructorDecl("C", ["A"], True, [])),
            ("type { :foo 4 } finite C A;", AstTypeConstructorDecl("C", ["A"], True, [AstAttribute("foo", [AstNumber(4)])])),
            ("type { :foo \"boo\" } finite C A;", AstTypeConstructorDecl("C", ["A"], True, [AstAttribute("foo", ["boo"])])),
        ]
        for (text, expectedAst) in good:
            try:
                t = (astBuilder.Decl + StringEnd()).parseString(text)[0]
            except ParseException:
                print("Failed parsing", text)
                raise
            assert t == expectedAst, "Expected: {} got {}".format(expectedAst, t)
