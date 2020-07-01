package org.abs_models.chisel.main

import java.io.File
import java.util.concurrent.TimeUnit

/**
 * Manages some piece of code that generates proof obligations, i.e., a class or the main block
 */
open class CodeContainer{
    protected var fields : MutableSet<String> = mutableSetOf(
        CONTRACTVARIABLE,
        RESULTVARIABLE,
        TIMEVARIABLE
    )


    private fun proofObligation(extraDefs: String,
                            prob: String,
                            prog : String,
                            path : String,
                            file : String,
                            extraFields : List<String> = emptyList(),
                            tactic : String = "expandAllDefs; master") : Boolean{

        val proof =
        """
        |Definitions
        |    HP skip ::= { ?true; };
        |    
        |    HP prog ::= {$prog};
        |    
        |    $extraDefs
        |    
        |End.
        |ProgramVariables
        |    ${(fields+extraFields).joinToString(" ") { "Real $it;" }}
        |End.
        |Problem
        |    $prob
        |End.
        |Tactic "default"
        |    $tactic
        |End.
        """.trimMargin()


        val f = File(path)
        f.mkdirs()
        File("$path/$file").writeText(proof)
        if(keymaeraPath != "") {
            val res = "java -jar $keymaeraPath -prove $path/$file".runCommand()
            if(res != null) {
                val answer = res.split("\n")
                output("starting keymaera x: java -jar $keymaeraPath -prove $path/$file")
                return answer[answer.size-2].startsWith("PROVED")
            }
        } else {
            output(proof)
        }

        return false

    }


    /* use this if obl contains no ODE*/
    fun proofObligationPure(obl: String,
                        pre: String,
                        prog : String,
                        path : String,
                        file : String,
                        extraFields : List<String> = emptyList()) : Boolean{
        var newpre = pre
        var newobl = obl
        fields.forEach { newpre = newpre.replace("$it'","${it}der"); newobl = newobl.replace("$it'","${it}der"); }

        val paramListDer = "${(fields+extraFields).joinToString(", ") { "Real $it" }}, ${(fields+extraFields).joinToString(", ") { "Real ${it}der" }}"
        val paramListCallSubst = "${(fields+extraFields).joinToString(", ") { it }}, ${(fields+extraFields).joinToString(", ") { "${it}'" }}"

        val extra =
            """
            |   Bool pre($paramListDer) <->
            |       (${newpre});
            |
            |   Bool post($paramListDer) <->
            |       (${newobl});
            """.trimMargin()
        val prob = """
            |   pre($paramListCallSubst)
            |   -> 
            |   [prog;](post($paramListCallSubst)) 
            """.trimMargin()

        return proofObligation(extra, prob, prog, path, file, extraFields)
    }

    /*pre -> [prog](dPost /\ [dynam]cPost)*/
    fun proofObligationComposed(
                        dPost: String,
                        dynam: String,
                        cPost: String,
                        pre: String,
                        prog : String,
                        path : String,
                        file : String,
                        extraFields : List<String> = emptyList(),
                        tactic : String) : Boolean{
        var newpre = pre
        var newcPost = cPost
        var newdPost = dPost
        fields.forEach {
            newpre = newpre.replace("$it'","${it}der")
            newcPost = newcPost.replace("$it'","${it}der")
            newdPost = newdPost.replace("$it'","${it}der")
        }


        val paramListDer = "${(fields+extraFields).joinToString(", ") { "Real $it" }}, ${(fields+extraFields).joinToString(", ") { "Real ${it}der" }}"
        val paramListCallSubst = "${(fields+extraFields).joinToString(", ") { it }}, ${(fields+extraFields).joinToString(", ") { "${it}'" }}"
        val extra =
            """
            |HP dynam ::= {$dynam};
            |
            |   Bool pre($paramListDer) <->
            |     (${newpre});
            |
            |   Bool cPost($paramListDer) <->
            |      (${newcPost});
            |
            |   Bool dPost($paramListDer) <->
            |       (${newdPost});
            """.trimMargin()
        val prob =
            """
            |pre($paramListCallSubst)
            |   -> 
            |   [prog;]
            |   (
            |       dPost($paramListCallSubst) 
            |       & ([dynam;]
            |           cPost($paramListCallSubst)
            |           )
            |   ) 
            """.trimMargin()

        return proofObligation(extra, prob, prog, path, file, extraFields, tactic)
    }


    /* https://stackoverflow.com/questions/35421699 */
    private fun String.runCommand(
        workingDir: File = File("."),
        timeoutAmount: Long = 60,
        timeoutUnit: TimeUnit = TimeUnit.SECONDS
    ): String? = try {
        ProcessBuilder(split("\\s".toRegex()))
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start().apply { waitFor(timeoutAmount, timeoutUnit) }
            .inputStream.bufferedReader().readText()
    } catch (e: java.io.IOException) {
        e.printStackTrace()
        null
    }
}