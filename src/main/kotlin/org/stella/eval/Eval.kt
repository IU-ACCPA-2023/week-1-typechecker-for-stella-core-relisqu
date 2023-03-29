package org.stella.eval

import org.stella.typecheck.TypeCheck
import org.syntax.stella.Absyn.Program
import org.syntax.stella.Absyn.Expr

object Eval {
    @Throws(Exception::class)
    fun evalMainWith(program: Program, inputExpr: Expr): Expr {
        TypeCheck.typecheckProgram(program)
        return inputExpr
    }
}
