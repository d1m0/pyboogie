""" 
Tests for implemented analyses
"""
from unittest import TestCase
from typing import Any, List, Tuple
from ..ast import parseAst, parseExprAst, AstExpr, AstStmt, parseStmt
from ..bb import Function
from ..predicate_transformers import wp_stmt, sp_stmt
from functools import reduce
from ..z3_embed import Z3TypeEnv, getCtx, Int, IntVal, BoolVal, And, Implies
from ..util import ccast
import z3

def _toExpr(a: Any) -> z3.ExprRef:
    return ccast(a, z3.ExprRef)

class TestPredicateTransformers(TestCase):
    testWPCases : List[Tuple[Any, str, Any, Z3TypeEnv]] = [
        (Int('y') == IntVal(4), "x:=y;", Int('x') == IntVal(4), {'x': Int, 'y': Int}),
        (Int('z') == IntVal(4), "x:=y;", Int('z') == IntVal(4), {'x': Int, 'y': Int}),
        (((Int('y') + IntVal(1)) == IntVal(4)), "x:=y+1;", Int('x') == IntVal(4), {'x': Int, 'y': Int}),
        (And(Int('y') == IntVal(4), Int('x') == IntVal(1)), "assert (x==1);", Int('y') == IntVal(4), {'x': Int, 'y': Int}),
        (Implies(_toExpr(Int('x') == IntVal(1)), _toExpr(Int('y') == IntVal(4))), "assume (x==1);", Int('y') == IntVal(4), {'x': Int, 'y': Int}),
        (Implies(_toExpr(Int('x') == IntVal(1)), _toExpr(Int('y') == IntVal(4))), "assume (x==1);", Int('y') == IntVal(4), {'x': Int, 'y': Int}),
    ]

    def testWPRequireSSA(self):
        """ 
        """
        with self.assertRaises(AssertionError):
            # predicate transformers assume code has been SSA-ed beforehand
            wp_stmt(parseStmt("x:=x+1;"), BoolVal(True), {'x': Int})

        with self.assertRaises(Exception):
            # predicate transformers assume code has been SSA-ed beforehand,
            # and in SSA-ing havocs get removed (they translate to bumps in SSA
            # indices)
            wp_stmt(parseStmt("havoc x;"), BoolVal(True), {'x': Int})

    def testWP(self):
        """ 
        """
        for (expected, stmt, post, typeEnv) in self.testWPCases:
            stmtAst = parseStmt(stmt)
            got = wp_stmt(stmtAst, post, typeEnv)
            assert z3.eq(got, expected), "Expected wp {} got {} from pred {} over stmt {}".format(expected, got, post, stmt)

    def testSPRequireSSA(self):
        """ 
        """
        with self.assertRaises(AssertionError):
            # predicate transformers assume code has been SSA-ed beforehand
            sp_stmt(parseStmt("x:=y;"), Int('x') == IntVal(4), {'x': Int, 'y': Int})

        with self.assertRaises(Exception):
            # predicate transformers assume code has been SSA-ed beforehand,
            # and in SSA-ing havocs get removed (they translate to bumps in SSA
            # indices)
            sp_stmt(parseStmt("havoc x;"), BoolVal(True), {'x': Int})

    testSPCases : List[Tuple[Any, str, Any, Z3TypeEnv]] = [
        (Int('y') == IntVal(4), "x:=y;", And(Int('x') == Int('y'), Int('y') == IntVal(4)), {'x': Int, 'y': Int}),
        (Int('z') == IntVal(4), "x:=y;", And(Int('x') == Int('y'), Int('z') == IntVal(4)), {'x': Int, 'y': Int, 'z': Int}),
        (Int('z') == IntVal(4), "x:=y+1;", And(Int('x') == (Int('y')+IntVal(1)), Int('z') == IntVal(4)), {'x': Int, 'y': Int, 'z': Int}),
        (Int('y') == IntVal(4), "assert (x==1);", And(Int('y') == IntVal(4), IntVal(1) == Int('x')), {'x': Int, 'y': Int}),
        (Int('y') == IntVal(4), "assume (x==1);", And(Int('y') == IntVal(4), IntVal(1) == Int('x')), {'x': Int, 'y': Int}),
    ]

    def testSP(self):
        """ 
        """
        for (pre, stmt, expected, typeEnv) in self.testSPCases:
            stmtAst = parseStmt(stmt)
            got = sp_stmt(stmtAst, pre, typeEnv)
            assert z3.eq(got, expected), "Expected sp {} got {} from pred {} over stmt {}".format(expected, got, pre, stmt)