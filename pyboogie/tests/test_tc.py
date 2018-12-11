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
from ..tc import tcExpr, tcStmt, tcDecl, tcProg, BTypeError, BType, BInt, BBool, Scope, BMap, BLambda, BProcedure, typeAccumulate
from typing import List, Tuple, Any

class TestExprTC(TestCase):
    goodExprs: List[Tuple[str, BType, Any]]= [
        ( "1", BInt(), ([], [])),
        ( "true", BBool(), ([], [])),
        ( "1+1", BInt(), ([], [])),
        ( "1<1", BBool(), ([], [])),
        ( "true<false", BBool(), ([], [])),
        ( "1<1 || false", BBool(), ([], [])),
        ( "1<1 ==> (4+5 == 9 mod 1)", BBool(), ([], [])),
        ( "-1", BInt(), ([], [])),
        ( "!false", BBool(), ([], [])),
        ( "a+1", BInt(), ([('a', BInt())], [])),
        ( "a+1 < 10 || b", BBool(), ([('a', BInt()), ('b', BBool())], [])),
        ( "a[10]", BBool(), ([('a', BMap([BInt()], BBool()))], [])),
        ( "a[c]", BBool(), ([('a', BMap([BInt()], BBool())), ('c', BInt())], [])),
        ( "a[10:=true]", BMap([BInt()], BBool()), ([('a', BMap([BInt()], BBool()))], [])),
        ( "(forall a: int :: a+1)", BInt(), ([], [])),
        ( "(forall a: int :: a+1)", BInt(), ([('a', BBool())], [])),
        ( "foo(10)", BBool(), ([], [('foo', BLambda((BInt(),), BBool()))])),
        ( "foo(10, b)", BBool(), ([('b', BBool())], [('foo', BLambda((BInt(),BBool()), BBool()))])),
        ( "foo(10, foo)", BBool(), ([('foo', BBool())], [('foo', BLambda((BInt(),BBool()), BBool()))])),
        ( "if true then 2 else 3", BInt(), ([], [])),
        ( "(forall a: int :: a+1)", BInt(), ([('a', BInt())], [])),
    ]

    badExprs: List[Tuple[str, Any, Any]]= [
        ( "1+true", [], []),
        ( "1<true", [], []),
        ( "1&&2", [], []),
        ( "1==>2", [], []),
        ( "!1", [], []),
        ( "-false", [], []),
        ( "a", [], []),
        ( "a+1", [('a', BBool())], []),
        ( "a[10]", [], []),
        ( "a[10]", [('a', BBool())], []),
        ( "a[10]", [('a', BMap([BBool()], BInt()))], []),
        ( "a[10]", [('a', BMap([BInt(), BBool()], BInt()))], []),
        ( "1+a[10]", [('a', BMap([BInt()], BBool()))], []),
        ( "a[10:=1]", [], []),
        ( "a[10:=1]", [('a', BBool())], []),
        ( "a[10:=1]", [('a', BMap([BBool()], BInt()))], []),
        ( "a[10:=1]", [('a', BMap([BInt(), BBool()], BInt()))], []),
        ( "a[10:=1]", [('a', BMap([BInt()], BBool()))], []),
        ( "if 1 then 2 else 3", [], []),
        ( "if true then 2 else false", [], []),
        ( "(forall a: int :: b+1)", [], []),
        ( "(forall a: int :: b+1)", [('b', BBool())], []),
        ( "(forall a: bool :: a+1)", [('a', BInt())], []),
        ( "foo(10)", [], []),
        ( "foo(10)", [('foo', BInt())], []),
        ( "foo(10)", [], [('foo', BLambda((), BInt()))]),
        ( "foo(10)", [], [('foo', BLambda((BBool(),), BInt()))]),
        ( "1+foo(10)", [], [('foo', BLambda((BInt(),), BBool()))]),
    ]
    def testGoodExprs(self):
        """ Make sure expr tc works on some good samples
        """
        for (exprText, expType, (vars, funs)) in self.goodExprs:
            expr = parseExprAst(exprText)
            varScope = Scope(None, None)
            funScope = Scope(None, None)
            for (name, typ) in vars:
                varScope.define(name, typ)
            for (name, typ) in funs:
                funScope.define(name, typ)
            env = (Scope(None, None), funScope, varScope, Scope(None, None))
            typ = tcExpr(expr, env)

            assert typ == expType, "Expected {} got {}".format(expType, typ)

    def testBadExprs(self):
        """ Make sure expr tc raises exceptions on type errors
        """
        for (exprText, vars, funs) in self.badExprs:
            expr = parseExprAst(exprText)
            varScope = Scope(None, None)
            funScope = Scope(None, None)
            for (name, typ) in vars:
                varScope.define(name, typ)
            for (name, typ) in funs:
                funScope.define(name, typ)
            env = (Scope(None, None), funScope, varScope, Scope(None, None))
            with self.assertRaises(BTypeError):
                tcExpr(expr, env)

class TestStmtTC(TestCase):
    goodStmts: List[Tuple[str, Any, Any, Any]]= [
        ( "return;", [], [], []),
        ( "goto foo;", [], [], []),
        ( "havoc a;", [('a', BInt())], [], []),
        ( "assume true;", [], [], []),
        ( "assume 3<4;", [], [], []),
        ( "assume a==1;", [('a', BInt())], [], []),
        ( "assert true;", [], [], []),
        ( "assert 3<4;", [], [], []),
        ( "assert a==1;", [('a', BInt())], [], []),
        ( "foo: return;", [('a', BInt())], [], []),
        ( "foo: assert a==1;", [('a', BInt())], [], []),
    ]

    badStmts: List[Tuple[str, Any, Any, Any]]= [
        ( "havoc a;", [], [], []),
        ( "assume 1;", [], [], []),
        ( "assume a==1;", [], [], []),
        ( "assert 1;", [], [], []),
        ( "assert a==1;", [], [], []),
        ( "foo: assert a==1;", [], [], []),
        ( "foo: havoc a;", [], [], []),
    ]

    def testGoodStmts(self):
        """ Make sure stmt tc works on some good samples
        """
        for (stmtText, vars, funs, procs) in self.goodStmts:
            stmt = parseStmt(stmtText)
            varScope = Scope(None, None)
            funScope = Scope(None, None)
            procScope = Scope(None, None)

            for (name, typ) in vars:
                varScope.define(name, typ)
            for (name, typ) in funs:
                funScope.define(name, typ)
            for (name, typ) in procs:
                procScope.define(name, typ)
            env = (Scope(None, None), funScope, varScope, procScope)
            tcStmt(stmt, env)

    def testBadStmts(self):
        """ Make sure stmt tc raises exceptions on type errors
        """
        for (stmtText, vars, funs, procs) in self.badStmts:
            stmt = parseStmt(stmtText)
            varScope = Scope(None, None)
            funScope = Scope(None, None)
            procScope = Scope(None, None)

            for (name, typ) in vars:
                varScope.define(name, typ)
            for (name, typ) in funs:
                funScope.define(name, typ)
            for (name, typ) in procs:
                procScope.define(name, typ)
            env = (Scope(None, None), funScope, varScope, procScope)
            with self.assertRaises(BTypeError):
                tcStmt(stmt, env)

class TestDeclTC(TestCase):
    goodDecls: List[Tuple[str, Any, Any, Any]]= [
            ( "var a: int;", [], [], []),
            ( "const a: int;", [], [], []),
            ( "function foo(a: int) returns (bool);", [], [], []),
            ( "function foo() returns (int) {1}", [], [], []),
            ( "function foo(a:int) returns (int) {a+1}", [], [], []),
            ( "procedure foo(a:int) returns (b:int) { b:= a+1; return; }", [], [], []),
            ( "procedure foo(a:int) returns (b:int) requires (a>0); ensures (b>0); modifies c; { b:= a+1; return; }", [('c', BBool())], [], []),
            ( "implementation foo(a:int) returns (b:int) { b:= a+1; return; }", [], [], [('foo', BProcedure((BInt(),), (BInt(),)))]),
            ( "axiom true;", [], [], []),
            ( "axiom a>0;", [('a', BInt())], [], []),
            ( "function sum(n:int) returns (int) { if (n==0) then 0 else n + sum(n-1) }", [], [], []),
            ( "procedure inf(n:int) returns (r: int) { call r:=inf(n-1); return; }", [], [], []),
    ]

    badDecls: List[Tuple[str, Any, Any, Any]]= [
            ( "function foo() returns (int) {true}", [], [], []),
            ( "function foo(a:int) returns (bool) {a+1}", [], [], []),
            ( "function foo(a:int) returns (int) {b+1}", [('b', BBool())], [], []),
            ( "procedure foo(a:int) returns (b:int) ;", [], [], [('foo', BProcedure((), ()))]),
            ( "procedure foo(a:int) returns (b:int) requires (a>0); ensures (b>0); modifies a; { b:= a+1; return; }", [], [], []),
            ( "procedure foo(a:int) returns (b:int) requires a+1; { b:= a+1; return; }", [], [], []),
            ( "procedure foo(a:int) returns (b:int) ensures a+1; { b:= a+1; return; }", [], [], []),
            ( "procedure foo(a:int) returns (b:int) ensures c==1; { b:= a+1; c:=1; return; }", [], [], []),
            ( "implementation foo(a:int) returns (b:int) { b:= a+1; return; }", [], [], []),
            ( "implementation foo(a:int) returns (b:int) { b:= a+1; return; }", [('foo', BInt())], [], []),
            ( "implementation foo(a:int) returns (b:int) { b:= a+1; return; }", [], [], []),
            ( "implementation foo(a:int) returns (b:int) { b:= a+1; return; }", [('foo', BInt())], [], []),
            ( "implementation foo(a:int) returns (b:int) { b:= a+1; return; }", [], [('foo', BLambda((BInt(),),BInt()))], []),
            ( "implementation foo(a:int) returns (b:int) { b:= a+1; return; }", [], [], [('foo', BProcedure((BBool(),), (BInt(),)))]),
            ( "axiom a>0;", [], [], []),
            ( "axiom a>0;", [('a', BBool())], [], []),
            ( "procedure inf(n:int) returns (r: int) { call r:=bar(n-1); return; }", [], [], []),
    ]

    def testGoodDecls(self):
        """ Make sure stmt tc works on some good samples
        """
        for (declText, vars, funs, procs) in self.goodDecls:
            decl = parseDecl(declText)
            varScope = Scope(None, None)
            funScope = Scope(None, None)
            procScope = Scope(None, None)

            for (name, typ) in vars:
                varScope.define(name, typ)
            for (name, typ) in funs:
                funScope.define(name, typ)
            for (name, typ) in procs:
                procScope.define(name, typ)
            env = (Scope(None, None), funScope, varScope, procScope)
            typeAccumulate(decl, env)
            tcDecl(decl, env)

    def testBadDecls(self):
        """ Make sure stmt tc raises exceptions on type errors
        """
        for (declText, vars, funs, procs) in self.badDecls:
            decl = parseDecl(declText)
            varScope = Scope(None, None)
            funScope = Scope(None, None)
            procScope = Scope(None, None)

            for (name, typ) in vars:
                varScope.define(name, typ)
            for (name, typ) in funs:
                funScope.define(name, typ)
            for (name, typ) in procs:
                procScope.define(name, typ)
            env = (Scope(None, None), funScope, varScope, procScope)
            with self.assertRaises(BTypeError):
                typeAccumulate(decl, env)
                tcDecl(decl, env)


class TestProgTC(TestCase):
    goodProgs: List[Tuple[str, Any]]= [
            ( "var a: int;", []),
            ( """var a: int;
                 procedure foo(b: int) returns (c:int) {
                    c:=a+b;
                    return;
                 }
              """, []),
            ("""type Foo X Y;
               var a: Foo int bool;
             """, []),
            ( """type Foo X Y;
                 var a: Foo int int;
                 procedure foo(b: Foo int int) returns (c:bool) {
                    c:=a<b;
                    return;
                 }
              """, []),
    ]

    badProgs: List[str]= [
            "function foo() returns (int) {true}",
            """type Foo X Y;
               var a: Foo int int;
               procedure foo(b: Foo int bool) returns (c:bool) {
                  c:=a<b;
                  return;
               }
            """,
            """type Foo X Y;
               var a: Foo Bad Type;
            """,
    ]

    def testGoodProgs(self):
        """ Make sure whole program tc works on some good samples
        """
        for (progText, _) in self.goodProgs:
            p = parseAst(progText)
            env = tcProg(p)

    def testBadDecls(self):
        """ Make sure whole program tc raises exceptions on type errors
        """
        for progText in self.badProgs:
            p = parseAst(progText)
            with self.assertRaises(BTypeError):
                tcProg(p)
