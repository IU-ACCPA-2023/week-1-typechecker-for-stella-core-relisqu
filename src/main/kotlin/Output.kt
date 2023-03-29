import org.syntax.stella.Absyn.Type
import org.syntax.stella.PrettyPrinter
import kotlin.system.exitProcess

/**
 * This class is used for test passing, as we throw this exception after string print
 */
class TypeException(message: String) : Exception(message)

/**
 * This class is used to throw errors for typechecking
 * @param assertExpression if true, the errors will not be thrown - is used for simple assertions
 */
class Output (assertExpression: Boolean){

    private val assertExpression: Boolean
    init {
        this.assertExpression = assertExpression
    }


    /**
     * Throws an error if the function has too few arguments
     * @param expression required count of arguments
     * @param got count of arguments that were given
     * @param line the line number
     * @param column the column number
     */
    fun ThrowFewArgumentsEr( exp: Int,got: Int, where: String) {
        if(assertExpression) return;
        throw TypeException("TYPE ERROR\n " +
                "in $where:\n " +
                "Expected $exp arguments, got $got arguments")
    }

    /**
     * Throws an error if the type of the expression is not the expected type
     * @param exp the expected type
     * @param got the type of the expression
     * @param line the line number
     * @param column the column number
     */
    fun ThrowExpectedGotEr(exp:Type, got: Type, where: String) {
        if(assertExpression) return;
        throw TypeException("TYPE ERROR\n " +
                "in $where:\n " +
                "Expected ${PrettyPrinter.print(exp)}, got ${PrettyPrinter.print(got)}")
    }

    /**
     * Throws an error if the two types differ from each other
     * @param first the first type
     * @param second the second type
     * @param where the string with line and symbol placement
     */
    fun ThrowExpectedEqTypes(first: Type, second: Type, where: String) {
        if (assertExpression) return;
        throw TypeException("TYPE ERROR\n " +
                "in $where:\n " +
                "Expected ${PrettyPrinter.print(first)} and ${PrettyPrinter.print(second)} to be equal types")
    }

    /** Throws an error if the variable is not defined
     * @param name the name of the variable
     * @param where the string with line and symbol placement
     */
    fun ThrowVariableNotDefinedEr(name: String, where: String) {
        if (assertExpression) return;
        throw TypeException("TYPE ERROR\n " +
                "in $where:\n " +
                "Variable $name is not defined")
    }
}