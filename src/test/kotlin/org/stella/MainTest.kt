package org.stella

import TypeException
import io.kotest.assertions.throwables.shouldNotThrowAny
import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.StringSpec
import java.io.File
import java.io.FileInputStream


class MainTest : StringSpec({

    File("src/test/resources").listFiles().forEach { dir ->
        val original = System.`in`
        "Test for ${dir.name}" {
            println("\n\nTest for ill-typed")
            File("src/test/resources/${dir.name}/ill-typed").listFiles().forEach { file ->
                println("\nTesting ${file.name}")
                val fips = FileInputStream(file)
                System.setIn(fips)
                shouldThrow<TypeException> {
                    //main(arrayOf<String>(file.absolutePath))
                    main()
                }
                System.setIn(original)
            }

            println("\n\nTest for well-typed")

            File("src/test/resources/${dir.name}/well-typed").listFiles().forEach { file ->
                println("\nTesting ${file.name}")
                val fips = FileInputStream(file)
                System.setIn(fips)
                shouldNotThrowAny{
                    //main(arrayOf<String>(file.absolutePath))
                    main()
                }
                System.setIn(original)

            }

        }
    }
})