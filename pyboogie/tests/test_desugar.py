""" 
Tests for basing Boogie parsing and AST building.
These tests focus on the core subset of boogie supported.
"""
from unittest import TestCase
from ..grammar import BoogieParser
from ..ast import parseAst, parseExprAst, parseStmt, parseDecl, AstProgram, AstImplementation,\
    AstBody, AstBinding, AstIntType, AstAssignment, AstId, AstBinExpr, \
    AstNumber, replace, AstMapIndex, AstMapUpdate, AstFuncExpr, AstMapType, \
    AstBoolType, AstBVType, AstCompoundType, parseType, \
    AstTypeConstructorDecl, astBuilder, AstAttribute, AstAssert, AstAssume,\
    AstIf, AstWildcard, AstTernary
from pyparsing import ParseException, StringEnd
from typing import List, Tuple, Any
from ..desugar import desugar
from ..util import resetUIDCtrs


class TestProgTC(TestCase):
    progs: List[Tuple[str, str]]= [
            ( "var a: int;", "var a: int;" ),
            ("""type Foo X Y;
               var a: Foo int bool;
             """, 
             """type Foo X Y;
               var a: Foo int bool;
             """),
            ( """var a: int;
                 procedure foo(b: int) returns (c:int) {
                    c:=a+b;
                    return;
                 }""", 
              """var a: int;
                 procedure foo(b: int) returns (c:int) {
                    __entry__:c:=a+b;
                    return;
                 }"""),
            ( """type Foo X Y;
                 var a: Foo int int;
                 procedure foo(b: Foo int int) returns (c:bool) {
                    c:=a<b;
                    return;
                 }""",
              """type Foo X Y;
                 var a: Foo int int;
                 procedure foo(b: Foo int int) returns (c:bool) {
                    __entry__: c:=a<b;
                    return;
                 }"""),
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry: c:=a<b;
                    return;
                 }"""),
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    goto then, else;
                    then:
                        assume c;
                        goto end;
                    else:
                        assume !c;
                        goto end;
                    end:
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    goto then, else;
                    then:
                        assume c;
                        goto end;
                    else:
                        assume !c;
                        goto end;
                    end:
                    return;
                 }"""),
            # One if statement
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    if (c) {

                    } else {

                    }
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    goto _then__0, _else__0;
                    _then__0:
                        assume c;
                        goto _union__0;
                    _else__0:
                        assume !c;
                        goto _union__0;
                    _union__0:
                    assert true;
                    return;
                 }"""),
            # Two consecutive if statements
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    if (c) {

                    } else {

                    }

                    if (c) {

                    } else {

                    }
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    goto _then__0, _else__0;
                    _then__0:
                        assume c;
                        goto _union__0;
                    _else__0:
                        assume !c;
                        goto _union__0;
                    _union__0:
                    assert true;
                    goto _then__1, _else__1;
                    _then__1:
                        assume c;
                        goto _union__1;
                    _else__1:
                        assume !c;
                        goto _union__1;
                    _union__1:
                    assert true;
                    return;
                 }"""),
            # If statement with no else
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    if (c) {

                    }
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a: int;
                    entry:
                    c:=a<b;
                    goto _then__0, _union__0;
                    _then__0:
                        assume c;
                        goto _union__0;
                    _union__0:
                    assert true;
                    return;
                 }"""),
            # If-else statement, no final else
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a, d: int;
                    entry:
                    c:=a<b;
                    if (c) {
                        d:=1;
                    } else if (a==0) {
                        d:=2;
                    } else if (b==0) {
                        d:=3;
                    }
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a, d: int;
                    entry:
                    c:=a<b;
                    goto _then__0, _else__0;
                    _then__0:
                        assume c;
                        d:=1;
                        goto _union__0;
                    _else__0:
                        assume !c;
                        goto _then__1, _else__1;
                    _then__1:
                        assume a == 0;
                        d:=2;
                        goto _union__1;
                    _else__1:
                        assume !(a == 0);
                        goto _then__2, _union__2;
                    _then__2:
                        assume (b == 0);
                        d := 3;
                        goto _union__2;
                    _union__2:
                        assert true;
                        goto _union__1;
                    _union__1:
                        assert true;
                        goto _union__0;
                    _union__0:
                        assert true;
                        return;
                 }"""),
            # If-else statement, with final else
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a, d: int;
                    entry:
                    c:=a<b;
                    if (c) {
                        d:=1;
                    } else if (a==0) {
                        d:=2;
                    } else if (b==0) {
                        d:=3;
                    } else {
                        d:=4;
                    }
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a, d: int;
                    entry:
                    c:=a<b;
                    goto _then__0, _else__0;
                    _then__0:
                        assume c;
                        d:=1;
                        goto _union__0;
                    _else__0:
                        assume !c;
                        goto _then__1, _else__1;
                    _then__1:
                        assume a == 0;
                        d:=2;
                        goto _union__1;
                    _else__1:
                        assume !(a == 0);
                        goto _then__2, _else__2;
                    _then__2:
                        assume (b == 0);
                        d := 3;
                        goto _union__2;
                    _else__2:
                        assume !(b==0);
                        d:=4;
                        goto _union__2;
                    _union__2:
                        assert true;
                        goto _union__1;
                    _union__1:
                        assert true;
                        goto _union__0;
                    _union__0:
                        assert true;
                        return;
                 }"""),
            # Nested if statements, no outer else
            ( """
                 procedure foo(b: int) returns (c:bool) {
                    var a, d: int;
                    entry:
                    c:=a<b;
                    if (c) {
                        d:=1;
                        if (a ==0) {
                            d:=2;
                        } else {
                            d:=3;
                        }
                        d:=4;
                    }
                    return;
                 }""",
              """
                 procedure foo(b: int) returns (c:bool) {
                    var a, d: int;
                    entry:
                    c:=a<b;
                    goto _then__0, _union__0;
                    _then__0:
                        assume c;
                        d:=1;
                        goto _then__1, _else__1;
                    _then__1:
                        assume (a==0);
                        d:=2;
                        goto _union__1;
                    _else__1:
                        assume !(a==0);
                        d:=3;
                        goto _union__1;

                    _union__1:
                        assert true;
                        d:=4;
                        goto _union__0;
                    _union__0:
                        assert true;
                        return;
                 }"""),
            ( """
                 procedure foo() {
                    var m: [int]int;
                    m[1] := 2;
                    return;
                 }""", 
              """
                 procedure foo() {
                    var m: [int]int;
                    __entry__:
                    m := m[1:= 2];
                    return;
                 }"""), 
            ( """
                 procedure foo() {
                    var m: [int][int]int;
                    m[1][2] := 3;
                    return;
                 }""", 
              """
                 procedure foo() {
                    var m: [int][int]int;
                    __entry__:
                    m := m[1:=m[1][2:=3]];
                    return;
                 }"""), 
            ( """
                 procedure foo() {
                    var m: [int,int]int;
                    m[1,2] := 3;
                    return;
                 }""", 
              """
                 procedure foo() {
                    var m: [int][int]int;
                    __entry__:
                    m := m[1,2:=3];
                    return;
                 }"""), 
    ]

    def test(self):
        """ Make sure whole program tc works on some good samples
        """
        for (progText, expectedText) in self.progs:
            resetUIDCtrs()
            p = parseAst(progText)
            desugaredP = desugar(p)
            expP = parseAst(expectedText)
            assert str(desugaredP) == str(expP), "Differing programs {} and {}".format(desugaredP, expP)