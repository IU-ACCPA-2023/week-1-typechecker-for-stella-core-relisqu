plugins {
    kotlin("jvm") version "1.8.0"
    id("io.kotest.multiplatform") version "5.0.2"
    application
}

group = "org.stella"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    implementation("org.antlr:antlr4:4.9.3")

    testImplementation(kotlin("test"))
    testImplementation("io.kotest:kotest-runner-junit5:5.5.5")
    testImplementation("io.kotest:kotest-assertions-core:5.5.5")
    implementation(kotlin("script-runtime"))
}

tasks.test {
    useJUnitPlatform()
    testLogging {
        events("passed", "skipped", "failed")
    }
}

kotlin {
    jvmToolchain(17)
}

application {
    mainClass.set("org.stella.MainKt")
}

tasks.named<JavaExec>("run") {
    standardInput = System.`in`
}
