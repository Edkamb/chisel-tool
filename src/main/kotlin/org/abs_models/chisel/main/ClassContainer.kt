package org.abs_models.chisel.main

import abs.frontend.ast.*
import java.io.File
const val CONTRACTVARIABLE = "contract"
open class CodeContainer{
    protected var fields : List<String> = listOf(CONTRACTVARIABLE)
    fun proofObligation(obl: String, path : String, file : String, extraFields : List<String> = emptyList()) : String{
        val proof =
            """
        Definitions
            HP skip ::= { ?true; };
        End.
        ProgramVariables
            ${(fields+extraFields).joinToString(" ") { "Real $it;" }}
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

class ClassContainer(private val cDecl : ClassDecl, private val reg : RegionOption) : CodeContainer(){
    private val name : String = cDecl.name
    private val pre = extractSpec(cDecl, "Requires")+" & contract = 1"
    private val inv =  extractSpec(cDecl.physical, "ObjInv")
    private val trPh = extractPhysical(cDecl.physical)


    init {
        if(reg == RegionOption.SplitRegion)
            throw Exception("option to use region $reg not supported yet")
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
        val res = proofObligation("$pre -> [$initialProg]$inv & contract = 1", "/tmp/chisel/$name", "init.kyx")
        output("First proof obligation:\n$res\n")
    }

    fun fill() {
        for(mDecl in cDecl.methods){
            val read  = collect(AssignStmt::class.java, mDecl).filter { it.`var` is FieldUse }
            if(read.isEmpty()){
                output("Skipping ${mDecl.methodSig.name} because it does not write into the heap")
                continue
            }

            val init = translateGuard(extractInitial(mDecl))
            val impl  = extractImpl(mDecl)
            val post = when(reg){
                RegionOption.BasicRegion -> {
                    if(impl.second) inv                          //if no field is accessed, the method needs only to check method calls
                    else            "($inv & contract = 1 & [{$trPh & true}]$inv)"
                }
                RegionOption.UniformRegion -> {
                    if(impl.second) inv
                    else{
                        val guards = impl.third.map { extractInitial(find(it, cDecl) )}
                        val dGuards = guards.filterIsInstance<DifferentialGuard>().map { "!("+translateGuard(it.condition)+")" }
                        val region = if (dGuards.isEmpty()) "true" else dGuards.joinToString( "&" )
                        "($inv & contract = 1 & [{$trPh & $region}]$inv)"
                    }
                }
                else -> throw Exception("option to use region $reg not supported yet")
            }
            val extraFields = mDecl.methodSig.paramList.map { it.name }
            val res = proofObligation("$inv -> [?$init;${impl.first}]$post", "/tmp/chisel/$name", "${mDecl.methodSig.name}.kyx", extraFields)
            output("Method proof obligation for ${mDecl.methodSig.name}:\n$res\n")

        }
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
    return physicalImpl.fields.joinToString(", ") {
        val exp = it.initExp as DifferentialExp
        if(exp.left is DiffOpExp){
            translateExpr(exp.left) + " =" + translateExpr(exp.right)
        } else throw Exception("Only ODEs are supported for translation to KeYmaera X, LHS found: ${exp.left}")
    }
}

fun extractInitial(mImpl : MethodImpl) : Guard?{
    val lead = mImpl.block.getStmt(0)
    return if(lead is AwaitStmt && lead.guard is DifferentialGuard){
        lead.guard
    }else null
}


fun extractImpl(mImpl : MethodImpl) : Triple<String, Boolean, Set<MethodSig>>{
    val init = if(extractInitial(mImpl) == null) 0 else 1
    val sofar = emptyList<String>().toMutableList()
    for(i in init .. mImpl.block.numStmt){
        sofar += translateStmt(mImpl.block.getStmt(i))
    }
    return Triple(sofar.joinToString(" "), isClean(mImpl.block), getCalled(mImpl.block))
}

