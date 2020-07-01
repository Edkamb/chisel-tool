package org.abs_models.chisel.main

import abs.frontend.ast.*

const val CONTRACTVARIABLE = "contract"
const val RESULTVARIABLE = "result"
const val TIMEVARIABLE = "tv"

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
        fields.addAll(cDecl.paramList.map { it.name })
        fields.addAll(cDecl.fields.map { it.name })
        fields.addAll(cDecl.physical.fields.map { it.name })

        //for the controlled Region we ensure that the class is controllable and fall back to uniform regions if it is not
        if(reg == RegionOption.CtrlRegion) {
            output("Class ${cDecl.name} is controllable: $controllable", Verbosity.VVV)
            if (controllable) {
                for (mImpl in cDecl.methods) {
                    if (isController(mImpl)) {
                        ctrlRegions.add(getCtrlRegion(mImpl))
                    }
                }
                output("controlled region: ${getRegionString()}", Verbosity.NORMAL)
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
        val init =  extractInitial(mImpl)
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
        var equalities = "true"
        for(fDecl in cDecl.fields ){
            equalities += " & ${fDecl.name} = ${translateExpr(fDecl.initExp)}"
        }
        for(fDecl in cDecl.physical.fields ) {
            val diffInit = fDecl.initExp as DifferentialExp
            equalities += "& ${fDecl.name} = ${translateExpr(diffInit.initVal)}"
            initialProg += ";${translateExpr(diffInit.left)} := ${translateExpr(diffInit.right)}"
        }
        initialProg += ";"
        val res = proofObligationPure(inv, "($pre) & ($equalities)", initialProg,"/tmp/chisel/$name", "init.kyx")
        output("Inital proof obligation result: \n$res\n", Verbosity.V)
        return res
    }

    fun proofObligationMethod(mDecl : MethodImpl) : Boolean{
        val read  = collect(AssignStmt::class.java, mDecl).filter { it.`var` is FieldUse }
        val call  = collectMustHaveCalled(mDecl.block, emptySet()) //collect(Call::class.java, mDecl)
        val mayCall  = collect(Call::class.java, mDecl)
        val create  = collect(NewExp::class.java, mDecl)
        if(read.isEmpty() && mayCall.isEmpty() && create.isEmpty() && extractSpec(mDecl,"Ensures") == "true"){
            output("Skipping ${mDecl.methodSig.name} because it does not write into the heap, makes no calls, creates no objects and has no Ensures specification")
            return true
        }


        val mSig = findInterfaceDecl(mDecl, mDecl.contextDecl as ClassDecl)
        val pre = "$inv & $CONTRACTVARIABLE = 1 & $TIMEVARIABLE = 0 & "+if(mSig != null){
            extractSpec(mSig,"Requires")
        } else "true"


        val init = translateGuard(extractInitial(mDecl))
        val impl  = extractImpl(mDecl)
        val post = "$CONTRACTVARIABLE = 1 & $inv & ${extractSpec(mDecl,"Ensures")}"
        val dynamics =
            if(read.isEmpty())  "skip"  else //if no field is accessed, the method needs only to check method calls
            when(reg){
            RegionOption.BasicRegion -> {
                "{$trPh & true}"
            }
            RegionOption.UniformRegion -> {
                val guards = call.map {  extractInitial(find(it.methodSig, cDecl) )}
                val dGuards = guards.filterIsInstance<DifferentialGuard>().map { "!("+translateGuard(it.condition)+")" }
                val region = if (dGuards.isEmpty()) "false" else dGuards.joinToString( "&" )
                " {$trPh, $TIMEVARIABLE' = 1 & $region}"
            }
            RegionOption.CtrlRegion -> {
                val guards = call.map {  extractInitial(find(it.methodSig, cDecl) )}
                val dGuards = guards.filterIsInstance<DifferentialGuard>().map { "!("+translateGuard(it.condition)+")" }
                var region = if (dGuards.isEmpty()) "false" else dGuards.joinToString( "&" )
                region = "$region & !(${getRegionString()})"
                " {$trPh, $TIMEVARIABLE' = 1 & $region}"
            }
        }
        val extraFields =  collect(VarUse::class.java,mDecl).map { it.name }//mDecl.methodSig.paramList.map { it.name } ++ collec
        val tactic = extractSpec(mDecl,"Tactic", default = "expandAllDefs; master")
        val res = proofObligationComposed(
            post,
            dynamics,
            inv,
            pre,"?$init;{$impl}","/tmp/chisel/$name", "${mDecl.methodSig.name}.kyx", extraFields, tactic)
        output("Method proof obligation for ${mDecl.methodSig.name}:\n$res\n", Verbosity.V)
        return res

    }

    private fun getRegionString() : String {
        if(ctrlRegions.isEmpty()) return "true"
        return ctrlRegions.joinToString(" & ")
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
    return if(lead is AwaitStmt && (lead.guard is DifferentialGuard || lead.guard is DurationGuard)){
        lead.guard
    }else null
}


fun extractImpl(mImpl: MethodImpl) : String{
    val init = if(extractInitial(mImpl) == null) 0 else 1
    val sofar = emptyList<String>().toMutableList()
    for(i in init until mImpl.block.numStmt){
        sofar += translateStmt(mImpl.block.getStmt(i))
    }
    return sofar.joinToString(" ")
}

