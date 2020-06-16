@file:Suppress("KotlinDeprecation", "KotlinDeprecation", "KotlinDeprecation", "KotlinDeprecation")

package org.abs_models.chisel.main

import abs.frontend.ast.*
import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.groups.default
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
        println("Chisel  : $text")
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


sealed class RegionOption{
    object BasicRegion : RegionOption()
    object UniformRegion : RegionOption()
    object SplitRegion : RegionOption()
}

class Main : CliktCommand() {
    private val filePath by argument(help = "path to ABS file").path().multiple()

    private val regionOpt : RegionOption by mutuallyExclusiveOptions<RegionOption>(
        option(help="Does not compute any regions").switch("--basic" to RegionOption.BasicRegion),
        option(help="Computes regions using the called methods").switch("--uniform" to RegionOption.UniformRegion),
        option(help="Computes regions using the called methods and controllers").switch("--split" to RegionOption.SplitRegion)
    ).single().default(RegionOption.BasicRegion)


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
        option("--directclass","-d",help="encodes <module>.<class> directly into a double loop structure (LITES approach)")
            .convert {  ChiselOption.DirectClassOption(it) as ChiselOption }
            .validate { require((it as ChiselOption.DirectClassOption).path.split(".").size == 2,
                lazyMessage = {"invalid fully qualified class name $it"}) },
        option(help="Verifies the main block of the model").switch("--main" to ChiselOption.MainBlockOption),
        option(help="Verifies the full model (not using -d)").switch("--full" to ChiselOption.FullOption)
    ).single().required()

    private val out        by   option("--out","-o",help="path to a directory used to store the .kyx files").path().default(Paths.get(outPath))
    private val verbose    by   option("--verbose", "-v",help="verbosity output level").int().restrictTo(Verbosity.values().indices).default(Verbosity.NORMAL.ordinal)

    override fun run() {
        verbosity = Verbosity.values()[verbose]
        outPath = "$out"

        output("Loading files....")
        val input = filePath.map{ File(it.toString()) }
        if(input.any { !it.exists() }) {
            System.err.println("file not found: $filePath")
            exitProcess(-1)
        }

        output("Loading ABS model....")
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
            is ChiselOption.MethodOption -> {
                val tt = target as ChiselOption.MethodOption
                proofObligationMethod(model, tt.path, regionOpt)
            }
            is ChiselOption.AllClassOption -> {
                val tt = target as ChiselOption.AllClassOption
                proofObligationsClass(model, tt.path, regionOpt)
            }
            is ChiselOption.InitOption -> {
                val tt = target as ChiselOption.InitOption
                proofObligationInit(model, tt.path, regionOpt)
            }
            is ChiselOption.FullOption -> {
                for(mDecl in model.moduleDecls.filter { !it.name.startsWith("ABS.") }){
                    for(cDecl in mDecl.decls.filterIsInstance<ClassDecl>()){
                        proofObligationsClass(model, mDecl.name+"."+cDecl.name,regionOpt)
                    }
                }
                proofObligationMainBlock(model)
            }
            is ChiselOption.MainBlockOption -> {
                proofObligationMainBlock(model)
            }
            else -> throw Exception("option $target not supported yet")
        }

        output("done")
    }
}


fun proofObligationMethod(model: Model, path : String, regionOpt : RegionOption) {
    val clazzCont = getContainer(model, path, regionOpt)
    val metDecl = clazzCont.cDecl.methods.firstOrNull { it.methodSig.name == path.split(".")[2] }
    if(metDecl == null) throw Exception("method not found")
    else                clazzCont.proofObligationMethod(metDecl)
}


fun proofObligationInit(model: Model, path : String, regionOpt : RegionOption) {
    val clazzCont = getContainer(model, path, regionOpt)
    clazzCont.proofObligationInitial()
}

fun proofObligationsClass(model: Model, path : String, regionOpt : RegionOption) {
    val clazzCont = getContainer(model, path, regionOpt)
    clazzCont.proofObligationsAll()
}

fun getContainer(model: Model, path : String, regionOpt : RegionOption) : ClassContainer{
    val mDecl = model.moduleDecls.firstOrNull { it.name == path.split(".")[0]}
    if(mDecl != null) {
        val cDecl = mDecl.declList.firstOrNull { it.name == path.split(".")[1]}
        if(cDecl != null && cDecl is ClassDecl) {
            if(cDecl.hasPhysical()) {
                return ClassContainer(cDecl, regionOpt)
            }
            else throw Exception("non-physical classes not supported, please use Crowbar instead")
        }
        else throw Exception("class not found")
    }
    else throw Exception("module not found")
}

fun proofObligationMainBlock(model: Model){
    val block = model.moduleDecls.firstOrNull { it.hasBlock() }?.block
    if(block == null) {
        System.err.println("Model contains no main block")
        exitProcess(-1)
    }
    val prog = translateStmt(block)
    val cc = CodeContainer()
    val vars = collect(VarUse::class.java,block).map { it.name }
    val res = cc.proofObligation("$CONTRACTVARIABLE = 1 -> [$prog]($CONTRACTVARIABLE = 1)","/tmp/chisel/main", "main.kyx",vars)
    output("Proof obligation for main block:\n$res\n")
}



fun main(args:Array<String>) = Main().main(args)