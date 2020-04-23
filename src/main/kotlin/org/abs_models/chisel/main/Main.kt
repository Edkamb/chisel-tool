package org.abs_models.chisel.main

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.types.path
import java.io.File
import kotlin.system.exitProcess

enum class Verbosity { SILENT, NORMAL, V, VV, VVV }


fun output(text : String, level : Verbosity = Verbosity.NORMAL){
    if(verbosity >= level)
        println(text)
}

var verbosity = Verbosity.NORMAL

class Main : CliktCommand() {
    private val filePath by argument(help = "path to ABS file").path().multiple()

    override fun run() {
        println("got $filePath")

        output("Crowbar  : loading files....")
        val input = filePath.map{ File(it.toString()) }
        if(input.any { !it.exists() }) {
            System.err.println("file not found: $filePath")
            exitProcess(-1)
        }

        output("Crowbar  : loading ABS model....")
        val model = try {
            abs.frontend.parser.Main().parse(input.map { it.toString() }.toTypedArray())
        } catch (e : Exception) {
            e.printStackTrace()
            System.err.println("error during parsing, aborting")
            exitProcess(-1)
        }
        if(model.hasTypeErrors())
            throw Exception("Compilation failed with type errors")

        println("done")
    }
}
fun main(args:Array<String>) = Main().main(args)