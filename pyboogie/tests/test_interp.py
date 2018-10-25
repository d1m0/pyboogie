"""
Tests for interp.py
"""

from unittest import TestCase
from ..grammar import BoogieParser
from ..ast import parseAst, parseExprAst, AstProgram, AstImplementation,\
    AstBody, AstBinding, AstIntType, AstAssignment, AstId, AstBinExpr, AstNumber, replace,\
    AstMapIndex, AstMapUpdate, AstFuncExpr, AstMapType, AstBoolType, ast_and, AstForallExpr
from ..interp import store_to_expr, map_to_expr, val_to_ast, FuncInterp, eval_quick
from ..ssa import SSAEnv

class TestInterp(TestCase):

	def testprimitives(self):
		tests = [
			({"a": 4}, AstBinExpr(AstId("a"), "==", val_to_ast(4))),
			({"a": 5, "b": 6}, ast_and([AstBinExpr(AstId("a"), "==", val_to_ast(5)),
										AstBinExpr(AstId("b"), "==", val_to_ast(6))])),
			({"t": False}, AstBinExpr(AstId("t"), "==", val_to_ast(False))),
			({"a": 4}, AstBinExpr(AstId("a"), "==", val_to_ast(4))),
		]

		for (text, expectedInterp) in tests:
			try:
				interpreted = store_to_expr(text)
			except:
				print ("Failed parsing {}".format(text))
				raise
			assert (interpreted == expectedInterp)
	
	def testmultiDim(self):
		ex = AstMapIndex(AstId("arr"), val_to_ast(0))
		tests = [
			(FuncInterp({0: FuncInterp({0: 1, 2: 3})}), ast_and([AstBinExpr(AstMapIndex(AstMapIndex(AstMapIndex(AstId("arr"), val_to_ast(0)),val_to_ast(0)), val_to_ast(0)),
													"==", val_to_ast(1)),
												AstBinExpr(AstMapIndex(AstMapIndex(AstMapIndex(AstId("arr"), val_to_ast(0)),val_to_ast(0)), val_to_ast(2)),
													"==", val_to_ast(3))])),
		]

		for (text, expectedInterp) in tests:
			try:
				interpreted = map_to_expr(text, ex)
				print(interpreted)
				print(expectedInterp)
			except:
				print ("Failed parsing {}".format(text))
				raise
			assert (interpreted == expectedInterp)

	def testEval(self):
		store = {"n": 3}
		tests = [
			(AstNumber(3), 3),
		]

		for (text, expectedInterp) in tests:
			try:
				evaluated = eval_quick(text,store)
				print(evaluated)
				print(expectedInterp)
			except:
				print ("Failed parsing {}".format(text))
				raise
			assert (evaluated == expectedInterp)