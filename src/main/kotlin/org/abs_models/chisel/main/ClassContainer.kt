package org.abs_models.chisel.main

import abs.frontend.ast.*
import java.io.File

class ClassContainer(private val cDecl : ClassDecl) {
    private val name : String = cDecl.name
    private val pre = extractSpec(cDecl, "Requires")
    private val inv =  extractSpec(cDecl.physical, "ObjInv")
    private val trPh = extractPhysical(cDecl.physical)

    private var fields : List<String> = emptyList()

    init {
        println("Chisel  : Extracted precondition $pre and invariant $inv for $name")
        var initialProg = "?true"
        for(fDecl in cDecl.paramList ){
            fields = fields + fDecl.name
        }
        for(fDecl in cDecl.fields ){
            fields += fDecl.name
            initialProg += ";${fDecl.name} := ${translateExpr(fDecl.initExp)}"
        }
        for(fDecl in cDecl.physical.fields ) {
            fields += fDecl.name
            val diffInit = fDecl.initExp as DifferentialExp
            initialProg += ";${fDecl.name} := ${translateExpr(diffInit.initVal)}"
        }
        initialProg += ";"
        val res = proofObligation("$pre -> [$initialProg]$inv", "/tmp/chisel/$name", "init.kyx")
        println("Chisel  : First proof obligation:\n$res")
    }

    fun fill() {
        for(mDecl in cDecl.methods){
            val init = translateGuard(extractInitial(mDecl))
            val impl  = extractImpl(mDecl)
            println("Chisel  : Found method ${mDecl.methodSig.name}")
            println("Chisel  :        with initial $init")
            println("Chisel  :        with implementation $impl")
            println("Chisel  :        with behavior $trPh & true")
            println("Chisel  :        proof obligation:")
            println("Chisel  :        $inv -> [?$init;$impl]($inv & [$trPh & true]$inv)")

        }
    }
    private fun proofObligation(obl: String, path : String, file : String) : String{
        val proof =
        """
        Definitions
            HP skip ::= { ?true; };
        End.
        ProgramVariables
            ${fields.joinToString(" ") { "Real $it;" }}
        End.
        Problem
            $obl
        End.
        """.trimIndent()
        val f = File(path)
        f.mkdirs()
        File("$path/$file").writeText(proof)
        return proof
    }
}


fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String, default:String = "true", multipleAllowed:Boolean = true) : String {
    var ret : String = default
    for (annotation in decl.nodeAnnotations) {
        if(!annotation.type.toString().endsWith(".HybridSpec")) continue
        if(annotation.getChild(0) !is DataConstructorExp) {
            throw Exception("Could not extract any specification $expectedSpec from $decl because of the expected value")
        }
        val annotated = annotation.getChild(0) as DataConstructorExp
        if(annotated.constructor != expectedSpec) continue
        val next = (annotated.getParam(0) as StringLiteral).content
        if (!multipleAllowed) break
        ret = "(($ret) & ($next))"
    }
    return ret
}

fun extractPhysical(physicalImpl: PhysicalImpl) : String{
    return physicalImpl.fields.joinToString(", ") { translateExpr(it.initExp) }
}

fun extractInitial(mImpl : MethodImpl) : Guard?{
    val lead = mImpl.block.getStmt(0)
    return if(lead is AwaitStmt){
        lead.guard
    }else null
}


fun extractImpl(mImpl : MethodImpl) : String{
    val init = if(extractInitial(mImpl) == null) 0 else 1
    val sofar = emptyList<String>().toMutableList()
    for(i in init .. mImpl.block.numStmt){
        sofar += translateStmt(mImpl.block.getStmt(i))
    }
    return sofar.joinToString(";")
}