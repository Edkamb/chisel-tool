package org.abs_models.chisel.main

import abs.frontend.ast.MethodSig
import java.io.File
import java.util.concurrent.TimeUnit

/**
 * Manages some piece of code that generates proof obligations, i.e., a class or the main block
 */
abstract class CodeContainer{
    protected var fields : MutableSet<String> = mutableSetOf(
        CONTRACTVARIABLE,
        RESULTVARIABLE,
        TIMEVARIABLE
    )

    abstract fun regionFor(extra : String, call : Set<MethodSig>) : String


    private fun proofObligation(extraDefs: String,
                            prob: String,
                            path : String,
                            file : String,
                            extraFields : List<String> = emptyList(),
                            tactic : String = "expandAllDefs; master") : Boolean{


        val proof =
        """
        |Definitions
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
                        prog : DlStmt,
                        placeholders : Set<String>,
                        path : String,
                        file : String,
                        extraFields : List<String> = emptyList(), tactic: String = "expandAllDefs; master") : Boolean{
        var newpre = pre
        var newobl = obl
        fields.forEach { newpre = newpre.replace("$it'","${it}der"); newobl = newobl.replace("$it'","${it}der"); }

        val paramListDer = "${(fields+extraFields).joinToString(", ") { "Real $it" }}, ${(fields+extraFields).joinToString(", ") { "Real ${it}der" }}"
        val paramListCallSubst = "${(fields+extraFields).joinToString(", ") { it }}, ${(fields+extraFields).joinToString(", ") { "${it}'" }}"

        var progTrans = prog.prettyPrint(2)
        for( check in placeholders ){
            progTrans = progTrans.replace(check, "true")
        }

        val extra =
            """
            |   HP skip ::= {?true;};
            |   Bool pre($paramListDer) <->
            |       (${newpre});
            |
            |   Bool post($paramListDer) <->
            |       (${newobl});
            """.trimMargin()
        val prob = """
            |   pre($paramListCallSubst)
            |   -> 
            |   [
            |$progTrans
            |   ](post($paramListCallSubst)) 
            """.trimMargin()

        return proofObligation(extra, prob, path, file, extraFields, tactic)
    }



    fun proofObligationNew(
        dPost: String,
        transRet: Triple<DlStmt, Set<MethodSig>, PlaceMap>,
        init: String,
        inv: String,
        pre: String,
        path: String,
        file: String,
        extraFields: List<String> = emptyList(),
        tactic: String = "expandAllDefs; master"
    ) : Boolean {

        //Abstract parameters
        var newpre = pre
        var newdPost = dPost
        fields.forEach {
            newpre = newpre.replace("$it'","${it}der")
            newdPost = newdPost.replace("$it'","${it}der")
        }
        val paramListDer = "${(fields+extraFields).joinToString(", ") { "Real $it" }}, ${(fields+extraFields).joinToString(", ") { "Real ${it}der" }}"
        val paramListCallSubst = "${(fields+extraFields).joinToString(", ") { it }}, ${(fields+extraFields).joinToString(", ") { "${it}'" }}"






        val progDefs =
            listOf(Pair("anon", fields.filter { it != CONTRACTVARIABLE }.joinToString (";",transform = {"$it := *" })+";"),
                   Pair("skip", "?true;"))


        val predDefs =
            listOf(Pair("pre", newpre),
                Pair("dPost", newdPost))


        var prog = transRet.first.prettyPrint(2)
        for(entry in transRet.third){
            prog = prog.replace(entry.key,"([${regionFor(entry.value.first, entry.value.second)}]$inv)")
        }


        val prob =
            """
            |pre($paramListCallSubst)
            |   -> 
            |   [
            |   ?$init;
            |   $prog
            |   ]
            |   (
            |       dPost($paramListCallSubst) 
            |       & 
            |       ([${regionFor("true", transRet.second)}]
            |         $inv)
            |   ) 
            """.trimMargin()

        val proof =
        """
        |Definitions
        |${progDefs.joinToString("\n") { "\tHP ${it.first} ::= {${it.second}};" }}
        |${predDefs.joinToString("\n") { "\tBool ${it.first}($paramListDer) <-> (${it.second});" }}
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

class SimpleGenerator  : CodeContainer(){
    override fun regionFor(extra: String, call: Set<MethodSig>): String = "true"
}