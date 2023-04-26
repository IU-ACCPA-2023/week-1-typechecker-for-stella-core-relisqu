package org.stella

import TypeException
import io.kotest.assertions.assertSoftly
import io.kotest.assertions.throwables.shouldNotThrowAny
import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.DescribeSpec
import java.io.File
import java.io.FileInputStream



class MainTest : DescribeSpec({
    File("src/test/resources").listFiles().forEach { dir ->
        val original = System.`in`
        assertSoftly {
            describe("Test for ${dir.name}") {
                describe("Test for ill-typed"){
                    File("src/test/resources/${dir.name}/ill-typed").listFiles().forEach { file ->
                        it("\nTesting ${file.name}") {
                            val fips = FileInputStream(file)
                            System.setIn(fips)

                            shouldThrow<TypeException> {
                                //main(arrayOf<String>(file.absolutePath))
                                main()
                            }
                            System.setIn(original)
                        }
                    }
                }
                describe("\n\nTest for well-typed") {

                    File("src/test/resources/${dir.name}/well-typed").listFiles().forEach { file ->
                        it("Testing ${file.name}") {

                            val fips = FileInputStream(file)
                            System.setIn(fips)
                            shouldNotThrowAny {
                                //main(arrayOf<String>(file.absolutePath))
                                main()
                            }
                            System.setIn(original)
                        }
                    }
                }
            }
        }
    }
})