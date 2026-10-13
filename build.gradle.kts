// dialysis-aut: the code of the paper "Refinement-Derived Algebraic Computation of Graph Automorphism Groups". One
// artefact matters: build/libs/dialysis-paper3.jar (task paperJar), a
// self-contained executable jar; see README.md.
plugins {
    kotlin("jvm") version "2.2.20"
}

group = "dialysis-aut"
version = "1.0"

repositories { mavenCentral() }

dependencies {
    implementation("org.jgrapht:jgrapht-core:1.5.2")   // DIMACS parsing in dialysis.util.GraphIO
    testImplementation(kotlin("test"))
}

// Native JNI libraries, built from source into src/main/resources and bundled in the jar:
//   libcoloredahu.so  colored AHU tree canonisation (used by the structural colouring PI)
//   libwl1jni.so      colour refinement (Paige-Tarjan style), the 1-WL backend
//   libtracesjni.so   vendored nauty/Traces 2.9.3 (src/main/cpp/nauty, Apache 2.0) -- for the separate oracle
//                     and baseline commands (oracle, traces); the method calls it only for the optional generator
//                     shortcut SERIES_GENAUT (group order via nauty's schreier.c, extension of the second paper).
val buildNativeAhu = tasks.register<Exec>("buildNativeAhu") {
    commandLine("bash", "src/main/cpp/build.sh")
    inputs.file("src/main/cpp/colored_ahu.cpp"); outputs.file("src/main/resources/libcoloredahu.so")
}
val buildNativeWl1 = tasks.register<Exec>("buildNativeWl1") {
    commandLine("bash", "src/main/cpp/build_wl1.sh")
    inputs.file("src/main/cpp/paige_tarjan_wl1.cpp"); outputs.file("src/main/resources/libwl1jni.so")
}
val buildNativeTraces = tasks.register<Exec>("buildNativeTraces") {
    commandLine("bash", "src/main/cpp/build_traces.sh")
    inputs.dir("src/main/cpp/nauty"); inputs.file("src/main/cpp/nauty_traces.cpp")
    outputs.file("src/main/resources/libtracesjni.so")
}
tasks.processResources { dependsOn(buildNativeAhu, buildNativeWl1, buildNativeTraces) }

// The experiment entry points live in the test source set (src/test/kotlin/dialysis/experimental): they are JUnit
// classes whose methods are whole campaigns driven by environment variables. They are run through the jar, never via
// `gradle test` (that would start every campaign), so the test task is disabled.
tasks.test { useJUnitPlatform(); enabled = false }   // useJUnitPlatform selects kotlin-test's JUnit 5 variant

val paperJar = tasks.register<Jar>("paperJar") {
    description = "Self-contained executable jar: java -jar build/libs/dialysis-paper3.jar series|chain|oracle|traces|run"
    archiveFileName.set("dialysis-paper3.jar")
    destinationDirectory.set(layout.buildDirectory.dir("libs"))
    dependsOn(tasks.named("testClasses"))
    manifest { attributes("Main-Class" to "Paper3Main") }
    from(sourceSets.main.get().output)
    from(sourceSets.test.get().output)
    from({ configurations.testRuntimeClasspath.get().filter { it.name.endsWith(".jar") }.map { zipTree(it) } })
    duplicatesStrategy = DuplicatesStrategy.EXCLUDE
    exclude("META-INF/*.SF", "META-INF/*.RSA", "META-INF/*.DSA", "META-INF/versions/**/module-info.class")
}
tasks.named("assemble") { dependsOn(paperJar) }
