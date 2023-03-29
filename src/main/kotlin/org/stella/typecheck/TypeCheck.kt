package org.stella.typecheck

import Output
import org.syntax.stella.Absyn.*

object TypeCheck {
    // class for storing the current variables in scope and their types
    class Context( var currentVars: MutableMap<String, Type> = mutableMapOf() ){
    }

    @Throws(Exception::class)
    fun typecheckProgram(program: Program) {
        val fullContext = Context(mutableMapOf())
        when (program) {
            is AProgram -> program.listdecl_.map {
                when (it) {
                    is DeclFun -> {  // if the declaration is a function declaration

                        val name = it.stellaident_
                        val returnType = it.returntype_
                        val params = it.listparamdecl_
                        val expr = it.expr_

                        val context = Context(fullContext.currentVars) // create a new context for the function scope
                        val paramTypes = ListType()
                        for (param in params) {
                            when (param) {
                                is AParamDecl -> {
                                    context.currentVars[param.stellaident_] = param.type_ // adding the parameter to the context
                                    paramTypes.add(context.currentVars[param.stellaident_])
                                }
                            }
                        }

                        val calculatedExpression = calculateExpression(Context(context.currentVars), expr) // calculating the type of func
                        context.currentVars[name] = TypeFun(paramTypes, calculatedExpression)  // saving function type to context

                        when (returnType) {
                            is SomeReturnType -> {
                                Output(returnType.type_ == calculatedExpression).
                                        ThrowExpectedGotEr( //check if return type is the same as the calculated type
                                            returnType.type_,
                                            calculatedExpression,
                                            "${returnType.line_num}:${returnType.col_num}"
                                        )
                            }
                        }

                    }


                }
            }

        }
    }

    /**
     * Returns the type of the expression and throw an error if the expression has typing errors
     * @param context the context of the scope with this expression
     * @param expr the expression
     * @return the calculated type of the expression
     */
    fun calculateExpression(context: Context, expr: Expr): Type {
        when (expr) {
            is ConstFalse, is ConstTrue -> return TypeBool()  //if it is just true or false, return bool
            is ConstInt -> { // if it is an integer, return Nat
                return TypeNat()
            }

            is If -> { //if it is an if expression, check if the condition is bool and the two expressions are the same type
                val ifCondition = calculateExpression(Context(context.currentVars), expr.expr_1)
                val trueExp = calculateExpression(Context(context.currentVars), expr.expr_2)
                val falseExp = calculateExpression(Context(context.currentVars), expr.expr_3)

                Output(trueExp == falseExp).
                        ThrowExpectedEqTypes(trueExp, falseExp, "${expr.line_num}:${expr.col_num}")

                Output(ifCondition == TypeBool()).ThrowExpectedGotEr(
                    TypeBool(),
                    ifCondition,
                    "${expr.line_num}:${expr.col_num}"
                )

                return trueExp
            }

            is Succ -> { //just check if the inner expression is Nat
                return checkIfExprIsNumber(Context(context.currentVars), expr.expr_, "${expr.line_num}:${expr.col_num}")
            }

            is Pred -> { // just check if the inner expression is Nat, same as Succ
                return checkIfExprIsNumber(Context(context.currentVars), expr.expr_, "${expr.line_num}:${expr.col_num}")
            }

            is NatRec -> {

                checkIfExprIsNumber(Context(context.currentVars), expr.expr_1, "${expr.line_num}:${expr.col_num}") //check if first expression is Nat

                val initValueType = calculateExpression(Context(context.currentVars), expr.expr_2)

                val expInp = ListType()
                expInp.add(initValueType)

                //need to check, if 3rd argument is a function with type fn(Nat) -> (fn(T) -> T), where T - type of initValueType
                when (val function = calculateExpression(Context(context.currentVars), expr.expr_3)) {
                    is TypeFun -> {
                        val paramSize = function.listtype_.size
                        Output(paramSize == 1). //check if the function has only one argument
                              ThrowFewArgumentsEr(1, paramSize, "${expr.line_num}:${expr.col_num}")

                        val paramType = function.listtype_[0]

                        Output(paramType == TypeNat()). //check if the parameter is Nat
                                ThrowExpectedGotEr(TypeNat(), paramType, "${expr.line_num}:${expr.col_num}")

                        val returnType = function.type_

                        Output(returnType == TypeFun(expInp, initValueType)).ThrowExpectedGotEr(
                            TypeFun( //check if the return type is fn(T) -> T
                                expInp,
                                initValueType
                            ), returnType, "${expr.line_num}:${expr.col_num}"
                        )

                    }
                    else ->{
                        Output(false).ThrowExpectedGotEr(
                            TypeFun(expInp, initValueType),
                            function,
                            "${expr.line_num}:${expr.col_num}"
                        )
                    }
                }
                return initValueType
            }

            is Application -> {

                val func = calculateExpression(Context(context.currentVars), expr.expr_) //evaluate the function type
                val args = ListType()
                for (i in expr.listexpr_) {
                    args.add(calculateExpression(Context(context.currentVars), i))
                }

                when (func) {
                    is TypeFun -> { //check if the function has 1 argument and it has the same type as the argument of application
                        if (func.listtype_.size == 1) {
                            Output(func.listtype_[0] == args[0]).ThrowExpectedGotEr(
                                func.listtype_[0],
                                args[0],
                                "${expr.line_num}:${expr.col_num}"
                            )
                        }
                        return func.type_
                    }

                    else -> {
                        Output(false).ThrowExpectedGotEr(
                            TypeFun(ListType(), TypeNat()),
                            func,
                            "${expr.line_num}:${expr.col_num}"
                        )
                    }
                }

            }

            is Var -> {  //check if the variable is defined and we can access it through the context
                Output(context.currentVars.containsKey(expr.stellaident_)).
                        ThrowVariableNotDefinedEr(
                            expr.stellaident_, "${expr.line_num}:${expr.col_num}"
                        )
                return context.currentVars[expr.stellaident_]!!
            }

            is Abstraction -> { //if we have a lambda expression, we need to calculate the type of the function
                val paramTypes = ListType()
                for (param in expr.listparamdecl_) {
                    when (param) {
                        is AParamDecl -> { //if we have a parameter, we just add it to the list of parameters
                            context.currentVars[param.stellaident_] = param.type_
                            paramTypes.add(param.type_)
                        }
                    }
                }

                val calculatedExpression = calculateExpression(Context(context.currentVars), expr.expr_) //calculate the type of the expression
                return TypeFun(paramTypes, calculatedExpression) //return the type of the function
            }

        }
        return TypeBool()

    }

    /**
     * Checks if the expression is a number and throws an error if it is not
     * @param context the context of the scope with this expression
     * @param expr the expression
     * @param where the place where this expression is (for error message if needed)
     * @return the calculated type of the expression
     */
    private fun checkIfExprIsNumber(context: Context, expr: Expr, where: String): Type {
        val innerExpr = calculateExpression(Context(context.currentVars), expr)
        Output(innerExpr == TypeNat()).
                ThrowExpectedGotEr(TypeNat(), innerExpr, where)

        return innerExpr
    }

}
