""" 
Tests for basing Boogie parsing and AST building.
These tests focus on the core subset of boogie supported.
"""
from unittest import TestCase
from ..grammar import BoogieParser
from ..ast import parseAst, parseExprAst, parseStmt, AstProgram, AstImplementation,\
    AstBody, AstBinding, AstIntType, AstAssignment, AstId, AstBinExpr, \
    AstNumber, replace, AstMapIndex, AstMapUpdate, AstFuncExpr, AstMapType, \
    AstBoolType, AstBVType, AstCompoundType, parseType, \
    AstTypeConstructorDecl, astBuilder, AstAttribute, AstAssert, AstAssume,\
    AstIf, AstWildcard, AstTernary
from pyparsing import ParseException, StringEnd
from ..tc import tcExpr, tcStmt, TypeError, BType, BInt, BBool, Scope, BMap, BLambda, BProcedure
from typing import List, Tuple, Any

class TestExprTC(TestCase):
    goodExprs: List[Tuple[str, BType, Any]]= [
        ( "1", BInt(), ([], [])),
        ( "true", BBool(), ([], [])),
        ( "1+1", BInt(), ([], [])),
        ( "1<1", BBool(), ([], [])),
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
    ]

    badExprs: List[Tuple[str, BType, Any]]= [
        ( "a[10:=1]", BMap([BInt()], BBool()), ([('a', BMap([BInt()], BBool()))], [])),
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
        for (exprText, expType, (vars, funs)) in self.badExprs:
            expr = parseExprAst(exprText)
            varScope = Scope(None, None)
            funScope = Scope(None, None)
            for (name, typ) in vars:
                varScope.define(name, typ)
            for (name, typ) in funs:
                funScope.define(name, typ)
            env = (Scope(None, None), funScope, varScope, Scope(None, None))
            with self.assertRaises(TypeError):
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
            with self.assertRaises(TypeError):
                tcStmt(stmt, env)
