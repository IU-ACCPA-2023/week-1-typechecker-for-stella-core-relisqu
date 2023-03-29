package org.stella

import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import java.io.File
import java.io.FileInputStream
import java.io.IOException

const val baseDir = "src/test/resources"
const val wellTypedDir = "$baseDir/well-typed"
const val illTypedDir = "$baseDir/ill-typed"

internal class MainTest {
    @ParameterizedTest(name = "{index} Typechecking well-typed program {0}")
    @ValueSource(strings = [
        "$wellTypedDir/factorial.stella",
        "$wellTypedDir/squares.stella",
        "$wellTypedDir/higher-order-1.stella",
        "$wellTypedDir/increment_twice.stella",
        "$wellTypedDir/logical-operators.stella",
        "$wellTypedDir/higher-order-2.stella",
        "$wellTypedDir/inner-if.stella"
    ])
    @Throws(
        IOException::class,
        Exception::class
    )
    fun testWellTyped(filepath: String) {
        val original = System.`in`
        val fips = FileInputStream(File(filepath))
        System.setIn(fips)
        main()
        System.setIn(original)
    }

    @ParameterizedTest(name = "{index} Typechecking ill-typed program {0}")
    @ValueSource(strings = [
        "$illTypedDir/applying-non-function-1.stella",
        "$illTypedDir/applying-non-function-2.stella",
        "$illTypedDir/applying-non-function-3.stella",
        "$illTypedDir/argument-type-mismatch-1.stella",
        "$illTypedDir/argument-type-mismatch-2.stella",
        "$illTypedDir/argument-type-mismatch-3.stella",
        "$illTypedDir/bad-if-1.stella",
        "$illTypedDir/bad-if-2.stella",
        "$illTypedDir/bad-succ-1.stella",
        "$illTypedDir/bad-succ-2.stella",
        "$illTypedDir/bad-succ-3.stella",
        "$illTypedDir/shadowed-variable-1.stella",
        "$illTypedDir/undefined-variable-1.stella",
        "$illTypedDir/undefined-variable-2.stella",
        "$illTypedDir/bad-squares-1.stella",
        "$illTypedDir/bad-squares-2.stella",
        "$illTypedDir/argument-type-mismatch-3.stella",
        "$illTypedDir/bad-if-3.stella"
    ])
    @Throws(
        IOException::class,
        Exception::class
    )
    fun testIllTyped(filepath: String) {
        val original = System.`in`
        val fips = FileInputStream(File(filepath))
        System.setIn(fips)
        var typecheckerFailed = false
        try {
          main()
        } catch (e: java.lang.Exception) {
            typecheckerFailed = true
        }
        if (!typecheckerFailed) {
            throw java.lang.Exception("expected the typechecker to fail!")
        }        // TODO: check that there is a type error actually, and not a problem with implementation
        System.setIn(original)
    }
}