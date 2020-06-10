@file:Suppress("KotlinDeprecation", "KotlinDeprecation", "KotlinDeprecation", "KotlinDeprecation")

package org.abs_models.chisel.main

import abs.frontend.ast.*
import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.groups.mutuallyExclusiveOptions
import com.github.ajalt.clikt.parameters.groups.required
import com.github.ajalt.clikt.parameters.groups.single
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.path
import com.github.ajalt.clikt.parameters.types.restrictTo
import java.io.File
import java.nio.file.Paths
import kotlin.system.exitProcess

var outPath = "."
enum class Verbosity { SILENT, NORMAL, V, VV, VVV }


fun output(text : String, level : Verbosity = Verbosity.NORMAL){
    if(verbosity >= level)
        println(text)
}

var verbosity = Verbosity.NORMAL

sealed class ChiselOption{
    data class MethodOption(val path : String) : ChiselOption()
    data class InitOption(val path : String) : ChiselOption()
    data class AllClassOption(val path : String) : ChiselOption()
    data class DirectClassOption(val path : String) : ChiselOption()
    object MainBlockOption : ChiselOption()
    object FullOption : ChiselOption()
}

class Main : CliktCommand() {
    private val filePath by argument(help = "path to ABS file").path().multiple()

    private val target : ChiselOption by mutuallyExclusiveOptions<ChiselOption>(
        option("--method","-m",help="Verifies a single method <module>.<class.<method>")
            .convert { ChiselOption.MethodOption(it) as ChiselOption }
            .validate { require((it as ChiselOption.MethodOption).path.split(".").size == 3,
                lazyMessage = {"invalid fully qualified method name $it"}) },
        option("--init","-i",help="Verifies the initial block of <module>.<class>")
            .convert {  ChiselOption.InitOption(it) as ChiselOption  }
            .validate { require((it as ChiselOption.InitOption).path.split(".").size == 2,
                lazyMessage = {"invalid fully qualified class name $it"}) },
        option("--class","-c",help="Verifies the initial block and all methods of <module>.<class>")
            .convert {  ChiselOption.AllClassOption(it) as ChiselOption }
            .validate { require((it as ChiselOption.AllClassOption).path.split(".").size == 2,
                lazyMessage = {"invalid fully qualified class name $it"}) },
        option("--directclass","-d",help="encodes <module>.<class> directly into a double loop structure")
            .convert {  ChiselOption.DirectClassOption(it) as ChiselOption }
            .validate { require((it as ChiselOption.AllClassOption).path.split(".").size == 2,
                lazyMessage = {"invalid fully qualified class name $it"}) },
        option(help="Verifies the main block of the model").switch("--main" to ChiselOption.MainBlockOption),
        option(help="Verifies the full model (not using -d)").switch("--full" to ChiselOption.FullOption)
    ).single().required()

    private val out        by   option("--out","-o",help="path to a directory used to store the .kyx files").path().default(Paths.get(outPath))
    private val verbose    by   option("--verbose", "-v",help="verbosity output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)

    override fun run() {
        println("got $filePath")
        verbosity = Verbosity.values()[verbose]
        outPath = "$out"

        output("Chisel  : loading files....")
        val input = filePath.map{ File(it.toString()) }
        if(input.any { !it.exists() }) {
            System.err.println("file not found: $filePath")
            exitProcess(-1)
        }

        output("Chisel  : loading ABS model....")
        val model = try {
            abs.frontend.parser.Main().parse(input.map { it.toString() }.toTypedArray())
        } catch (e : Exception) {
            e.printStackTrace()
            System.err.println("error during parsing, aborting")
            exitProcess(-1)
        }
        if(model.hasTypeErrors())
            throw Exception("Compilation failed with type errors")

        when(target) {
            is ChiselOption.AllClassOption -> {
                val tt = target as ChiselOption.AllClassOption
                val mDecl = model.moduleDecls.firstOrNull { it.name == tt.path.split(".")[0]}
                if(mDecl != null) {
                    val cDecl = mDecl.declList.firstOrNull { it.name == tt.path.split(".")[1]}
                    if(cDecl != null && cDecl is ClassDecl) {
                        if(cDecl.hasPhysical()) {
                            val clazzCont = ClassContainer(cDecl)
                            clazzCont.fill()
                        }
                        else throw Exception("non-physical classes not supported, please use Crowbar instead")
                    }
                    else throw Exception("class not found")
                }
                else throw Exception("module not found")
            }
            else -> throw Exception("not supported yer")
        }

        println("done")
    }
}



fun main(args:Array<String>) = Main().main(args)