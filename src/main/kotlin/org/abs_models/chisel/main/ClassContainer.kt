package org.abs_models.chisel.main

import abs.frontend.ast.*
import java.io.File
import java.util.concurrent.TimeUnit

const val CONTRACTVARIABLE = "contract"
const val RESULTVARIABLE = "result"

/**
 * Manages some piece of code that generates proof obligations, i.e., a class or the main block
 */
open class CodeContainer{
    protected var fields : Set<String> = setOf(CONTRACTVARIABLE,RESULTVARIABLE)
    fun proofObligation(obl: String, path : String, file : String, extraFields : List<String> = emptyList()) : Boolean{
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
        Tactic "default"
            US("skip;~>?true;") ; master
        End.
        """.trimIndent()
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

/**
 * reg is variable because we may fall back to uniform regions if the class is not controllable
 */
class ClassContainer(val cDecl : ClassDecl, private var reg : RegionOption) : CodeContainer(){
    private val name : String = cDecl.name

    //these are unprocessed user inputs
    private val pre = extractSpec(cDecl, "Requires")+" & contract = 1"
    private val inv =  extractSpec(cDecl.physical, "ObjInv")
    private val trPh = extractPhysical(cDecl.physical)
    private val controllable = isControllable()
    private var ctrlRegions = mutableListOf<String>()

    init {
        //for the controlled Region we ensure that the class is controllable and fall back to uniform regions if it is not
        if(reg == RegionOption.CtrlRegion) {
            output("Class ${cDecl.name} is controllable: $controllable", Verbosity.VVV)
            if (controllable) {
                for (mImpl in cDecl.methods) {
                    if (isController(mImpl)) {
                        ctrlRegions.add(getCtrlRegion(mImpl))
                    }
                }
                output("controlled region: ${ctrlRegions.joinToString(" & ")}", Verbosity.VVV)
            }else {
                output("Class ${cDecl.name} is not controllable, falling back to uniform regions", Verbosity.NORMAL)
            }
        }
    }

    //xxx: we do not check that run is not exposed
    /**
     * This checks that the class is controllable:
     *  - no gets
     *  - no durations
     *  - no synchronous calls (for simplicity)
     *  - no calls to run
     *  - run is a sequence of asynchronous calls
     */
    private fun isControllable() : Boolean{
        val runSig = cDecl.methods.map { it.methodSig }.firstOrNull { it.name == "run" } ?: return false
        for(mImpl in cDecl.methods){
            if(mImpl.methodSig.matches(runSig)) {
                for (i in 0 until mImpl.block.numStmt) {
                    if(mImpl.block.getStmt(i) !is ExpressionStmt || (mImpl.block.getStmt(i) as ExpressionStmt).exp !is AsyncCall) return false
                }
            } else {
                val init = if (extractInitial(mImpl) == null) 0 else 1
                for (i in init until mImpl.block.numStmt) {
                    if (collect(GetExp::class.java, mImpl.block.getStmt(i)).isNotEmpty())
                        return false
                    if (collect(DurationStmt::class.java, mImpl.block.getStmt(i)).isNotEmpty())
                        return false
                    if (collect(SyncCall::class.java, mImpl.block.getStmt(i)).isNotEmpty())
                        return false
                    if (collect(Call::class.java, mImpl.block.getStmt(i)).any { it.methodSig.matches(runSig) })
                        return false
                }
            }
        }
        return true
    }

    private fun getCtrlRegion(mImpl: MethodImpl) : String{
        val init =  extractInitial(mImpl) as DifferentialGuard
        return translateGuard(init)
    }

    /**
     *  This methods assumes isControllable()
     *
     *  Checks whether the method is a controller method:
     *   - is called from run
     *   - starts with an await
     *   - no awaits otherwise
     *   - last statement is an asynchronous recursive call
     */
    private fun isController(mImpl: MethodImpl): Boolean {
        if(extractInitial(mImpl) == null) return false
        val finalCall =  mImpl.block.getStmt(mImpl.block.numStmt-1)
        if(finalCall is ExpressionStmt && finalCall.exp is AsyncCall) {
            val vv = finalCall.exp as AsyncCall
            if (vv.callee is ThisExp && vv.methodSig.matches(mImpl.methodSig)) {
                for (i in 1 until mImpl.block.numStmt - 1) {
                    if (collect(AwaitStmt::class.java, mImpl.block.getStmt(i)).isNotEmpty())
                        return false
                }

                val runImpl = cDecl.methods.first { it.methodSig.name == "run" }
                return collect(Call::class.java, runImpl).any { it.methodSig.matches(mImpl.methodSig) }
            }
        }
        return false
    }

    //TODO: this does not handle run correctly
    fun proofObligationInitial() : Boolean{
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
        output("Inital proof obligation result: \n$res\n", Verbosity.V)
        return res
    }

    fun proofObligationMethod(mDecl : MethodImpl) : Boolean{
        val read  = collect(AssignStmt::class.java, mDecl).filter { it.`var` is FieldUse }
        val call  = collect(Call::class.java, mDecl)
        val create  = collect(NewExp::class.java, mDecl)
        if(read.isEmpty() && call.isEmpty() && create.isEmpty() && extractSpec(mDecl,"Ensures") == "true"){
            output("Skipping ${mDecl.methodSig.name} because it does not write into the heap, makes no calls, creates no objects and has no Ensures specification")
            return true
        }


        val mSig = findInterfaceDecl(mDecl.model, mDecl, mDecl.contextDecl as ClassDecl)
        val pre = "$inv & $CONTRACTVARIABLE = 1 & "+if(mSig != null){
            extractSpec(mSig,"Requires")
        } else "true"


        val init = translateGuard(extractInitial(mDecl))
        val impl  = extractImpl(mDecl) //todo: .second is no checked with read above
        var post = "(${CONTRACTVARIABLE} = 1 & $inv & ${extractSpec(mDecl,"Ensures")}"
        post +=
            if(read.isEmpty())  ")"  else //if no field is accessed, the method needs only to check method calls
                when(reg){
            RegionOption.BasicRegion -> {
                " & [{$trPh & true}]$inv)"
            }
            RegionOption.UniformRegion -> {
                val guards = call.map {  extractInitial(find(it.methodSig, cDecl) )}
                val dGuards = guards.filterIsInstance<DifferentialGuard>().map { "!("+translateGuard(it.condition)+")" }
                val region = if (dGuards.isEmpty()) "true" else dGuards.joinToString( "&" )
                " & [{$trPh & $region}]$inv)"
            }
            RegionOption.CtrlRegion -> {
                val guards = call.map {  extractInitial(find(it.methodSig, cDecl) )}
                val dGuards = guards.filterIsInstance<DifferentialGuard>().map { "!("+translateGuard(it.condition)+")" }
                var region = if (dGuards.isEmpty()) "true" else dGuards.joinToString( "&" )
                region = "$region & !(${ctrlRegions.joinToString(" & ")})"
                " & [{$trPh & $region}]$inv)"
            }
        }
        val extraFields =  collect(VarUse::class.java,mDecl).map { it.name }//mDecl.methodSig.paramList.map { it.name } ++ collec
        val res = proofObligation("$pre -> [?$init;{$impl}]$post", "/tmp/chisel/$name", "${mDecl.methodSig.name}.kyx", extraFields)
        output("Method proof obligation for ${mDecl.methodSig.name}:\n$res\n", Verbosity.V)
        return res

    }

    fun proofObligationsAll() : Boolean{
        var res = proofObligationInitial()
        output("verification result for ${cDecl.name}.<init>: $res")
        for(mDecl in cDecl.methods){
            val next =  proofObligationMethod(mDecl)
            output("verification result for ${cDecl.name +"."+mDecl.methodSig.name}: $next")
            res = res && next
        }
        return res
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


fun extractImpl(mImpl : MethodImpl) : String{
    val init = if(extractInitial(mImpl) == null) 0 else 1
    val sofar = emptyList<String>().toMutableList()
    for(i in init until mImpl.block.numStmt){
        sofar += translateStmt(mImpl.block.getStmt(i))
    }
    return sofar.joinToString(" ")
}

