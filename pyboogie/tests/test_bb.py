""" 
Tests for building BBs/Functions out of a simple parse tree.
"""
from unittest import TestCase
from ..grammar import BoogieParser
from ..ast import parseAst, parseExprAst, AstProgram, AstImplementation,\
    AstBody, AstBinding, AstIntType, AstAssignment, AstId, AstBinExpr, AstNumber, replace,\
    parseBinding
from ..bb import BB, Function, Bindings_T
from typing import Any, List
from functools import reduce

class TestBB(TestCase):
    testProgs = [
        (# Empty program
            """
                implementation main() {
                }
            """,
            ["main", [], [], [], [("__dummy_exit__", [], [], [])]]
        ),
        (# Empty program with a variable definition
            """
                implementation main() {
                    var x: int;
                }
            """,
            ["main", [], [("x", "int")], [], [("__dummy_exit__", [], [], [])]]
        ),
        (# Program with a variable definition and single BB
            """
                implementation main() {
                    var x: int;
                    
                foo:
                    x := x+42;
                }
            """,
            ["main", [], [("x", "int")], [], [("foo", [], ["x:=x+42;"], [])]]
        ),
        (# Program with a variable definition,an empty BB and a normal bb
            """
                implementation main() {
                    var x: int;
                foo:
                boo:
                    x := 1;
                }
            """,
            ["main", [], [("x", "int")], [], [("foo", [], [], ["boo"]), ("boo", [], ["x:=1;"], [])]]
        ),
        (# Program with a variable definition,and only an empty BB
            """
                implementation main() {
                    var x: int;
                foo:
                }
            """,
            ["main", [], [("x", "int")], [], [("foo", [], [], [])]]
        ),
        (# If statement
            """
                implementation main() {
                    var x,y: int;
                start:
                    goto then, else;
                then:
                    assert (x>0);
                    y:=1;
                    goto end;
                else:
                    assert (x<=0);
                    y:=2;
                    goto end;
                end:
                }
            """,
            ["main", [], [("x", "int"), ("y", "int")], [], [
                ("start", [], [], ["then", "else"]),
                ("then", ["start"], ["assert x>0;", "y:=1;"], ["end"]),
                ("else", ["start"], ["assert x<=0;", "y:=2;"], ["end"]),
                ("end", ["start", "else"], [], []),
                ]
            ]
        ),
        (# Simple loop
            """
                implementation main() {
                    var x,y: int;
                start:
                    x := 0;
                    assume (n>0);
                    goto header;
                header:
                    goto body, end;
                body:
                    assume (x<n);
                    x := x+1;
                    goto header;
                end:
                    assume(x >= n);
                }
            """,
            ["main", [], [("x", "int"), ("y", "int")], [], [
                ("start", [], ["x:=0;", "assume n>0;"], ["header"]),
                ("header", ["start"], [], ["body", "end"]),
                ("body", ["header"], ["assume x<n;", "x:=x+1;"], ["header"]),
                ("end", ["header"], ["assume x>=n;"], []),
                ]
            ]
        ),
        (# One dimensional map assignment
            """
                implementation main() {
                    var x: [int]int;
                    var y: int;
                start:
                    x[y] := 0;
                }
            """,
            ["main", [], [("x", "[int]int"), ("y", "int")], [], [
                ("start", [], ["x:=x[y:=0];"], []),
                ]
            ]
        ),
        (# Two dimensional map assignment
            """
                implementation main() {
                    var x: [int][int]int;
                    var y,z: int;
                start:
                    x[y][z] := 0;
                }
            """,
            ["main", [], [("x", "[int][int]int"), ("y", "int"), ("z", "int")], [], [
                ("start", [], ["x:=x[y:=x[y][z:=0]];"], []),
                ]
            ]
        ),
    ]
    badProgs = [
        """
            implementation main() {
                var x: int;
                x := 1;
            }
        """,
        """
            implementation main() {
                var x: int;
                x := 1;
                foo:
            }
        """,
        """
            implementation main() {
                var x: int;
            foo:
                goto bar;
                x := 1;
            bar:
            }
        """,
    ]

    def test_build(self):
        """ For each pair of text S and expected program P in
            TestAst.testProgs check Function.build(parseExpr(S)[0][0]) == P
        """
        for (text, expected) in self.testProgs:
            prog = parseAst(text) # type: AstProgram
            assert(len(prog.decls) == 1)
            root = Function.build(prog.decls[0])
            try:
                expectedF = Function.from_json(expected)
                assert (expectedF.eq(root))
            except AssertionError:
                print ("Got {} expeced {}".format(root.pp(), expectedF.pp()))
                raise

    def test_build_fail(self):
        """ Make sure Function.build fails for malformed programs. We expect several rules to work to build a 
            Function from an AstImplementation:
                1. Every statement occurs between a label and a goto
                2. Every label in a goto is defined
        """
        for (text) in self.badProgs:
            prog = parseAst(text) # type: AstProgram
            with self.assertRaises(AssertionError):
                Function.build(prog.decls[0])