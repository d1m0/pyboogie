from .ast import AstLabel, AstAssignment, AstAssert, AstAssume, \
        expr_read, AstStmt, AstId, stmt_read
from .z3_embed import expr_to_z3, And, Implies, ids, Z3TypeEnv, _force_expr
from .util import ccast
from collections import namedtuple
import z3
from typing import Iterable, Reversible, List

# Note: These predicate transformers are not fully general - they
# expect code to be SSA-ed first.

def wp_stmt(stmt: AstStmt, pred: z3.ExprRef, typeEnv: Z3TypeEnv) -> z3.ExprRef:
    if (isinstance(stmt, AstLabel)):
        stmt = stmt.stmt

    if (isinstance(stmt, AstAssignment)):
        read = stmt_read(stmt)
        for (lhs, rhs) in zip(stmt.lhs, stmt.rhs):
            assignee = str(lhs)
            # Should already be SSA-ed
            assert(assignee not in read)
            z3lhs = typeEnv[assignee](assignee)
            z3rhs = expr_to_z3(rhs, typeEnv)
            pred = _force_expr(z3.substitute(pred, (z3lhs, z3rhs)))
        return pred
    elif (isinstance(stmt, AstAssert)):
        return And(pred, expr_to_z3(stmt.expr, typeEnv))
    elif (isinstance(stmt, AstAssume)):
        return Implies(expr_to_z3(stmt.expr, typeEnv), pred)
    else:
        raise Exception("Cannot handle Boogie Statement: " + str(stmt))

def wp_stmts(stmts: Reversible[AstStmt], pred: z3.ExprRef, typeEnv: Z3TypeEnv) -> z3.ExprRef:
    for s in reversed(stmts):
        #old_pred = pred
        pred = wp_stmt(s, pred, typeEnv)
        #print "WP of ", old_pred, " w.r.t. ", s, " is ", pred
    return pred

def sp_stmt(stmt: AstStmt, pred: z3.ExprRef, typeEnv: Z3TypeEnv) -> z3.ExprRef:
    if (isinstance(stmt, AstLabel)):
        stmt = stmt.stmt

    if (isinstance(stmt, AstAssignment)):
        read = stmt_read(stmt)
        preds: List[z3.ExprRef] = []
        for (lhs,rhs) in zip(stmt.lhs, stmt.rhs):
            assignee = str(lhs)
            # Should already be SSA-ed
            assert(assignee not in read and \
                  (assignee not in set(map(str, ids(pred)))))
            z3lhs = expr_to_z3(lhs, typeEnv)
            z3rhs = expr_to_z3(rhs, typeEnv)
            preds.append(ccast(z3lhs == z3rhs, z3.ExprRef))

        preds.append(pred)
        return And(*preds)
    elif (isinstance(stmt, AstAssert)):
        return And(pred, expr_to_z3(stmt.expr, typeEnv))
    elif (isinstance(stmt, AstAssume)):
        return And(pred, expr_to_z3(stmt.expr, typeEnv))
    else:
        raise Exception("Cannot handle Boogie Statement: " + str(stmt))

def sp_stmts(stmts: Iterable[AstStmt], pred: z3.ExprRef, typeEnv: Z3TypeEnv) -> z3.ExprRef:
    for s in stmts:
        pred = sp_stmt(s, pred, typeEnv)
    return pred
