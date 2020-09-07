package org.abs_models.chisel.main

import abs.frontend.ast.*
import java.io.File

const val CONTRACTVARIABLE = "contract"
const val RESULTVARIABLE = "result"
const val TIMEVARIABLE = "tv"
const val ZENOLIMITVARIABLE = "zlimitvar"

/**
 * reg is variable because we may fall back to uniform regions if the class is not controllable
 */
class ClassContainer(val cDecl : ClassDecl, private var reg : RegionOption) : CodeContainer(){
    private val name : String = cDecl.name

    //these are unprocessed user inputs
    private val pre = extractSpec(cDecl, "Requires")+" & $CONTRACTVARIABLE = 1"
    private val inv =  extractSpec(cDecl.physical, "ObjInv")
    private val trPh = extractPhysical(cDecl.physical)
    private var ctrlRegions = mutableListOf<String>()

    init {
        fields.addAll(cDecl.paramList.map { it.name })
        fields.addAll(cDecl.fields.map { it.name })
        fields.addAll(cDecl.physical.fields.map { it.name })

        //for the controlled Region we ensure that the class is controllable and fall back to uniform regions if it is not
        if(reg == RegionOption.CtrlRegion) {
            for (mImpl in cDecl.methods) {
                if (isController(mImpl)) ctrlRegions.add(getCtrlRegion(mImpl))
            }
            output("controlled region: ${getRegionString()}", Verbosity.NORMAL)
        }
    }

    private fun getCtrlRegion(mImpl: MethodImpl) : String{
        val init =  extractInitial(mImpl)
        return translateGuard(init)
    }

    /**
     *  Checks whether the method is a controller method:
     *   - is called from init block
     *   - starts with an await
     *   - no awaits otherwise
     *   - last statement is an asynchronous recursive call
     */
    private fun isController(mImpl: MethodImpl): Boolean {
        if(extractInitial(mImpl) == null) return false
        if(cDecl.initBlock == null) return false
        val finalCall =  mImpl.block.getStmt(mImpl.block.numStmt-1)
        if(finalCall is ExpressionStmt && finalCall.exp is AsyncCall) {
            val vv = finalCall.exp as AsyncCall
            if (vv.callee is ThisExp && vv.methodSig.matches(mImpl.methodSig)) {
                for (i in 1 until mImpl.block.numStmt - 1) {
                    if (collect(AwaitStmt::class.java, mImpl.block.getStmt(i)).isNotEmpty())
                        return false
                }
                val runImpl = cDecl.initBlock
                return collect(Call::class.java, runImpl).any { it.methodSig.matches(mImpl.methodSig) }
            }
        }
        return false
    }

    fun proofObligationInitial() : Boolean{
        var equalities = "$CONTRACTVARIABLE = 1"
        for(fDecl in cDecl.fields ){
            equalities += " & ${fDecl.name} = ${translateExpr(fDecl.initExp)}"
        }
        for(fDecl in cDecl.physical.fields ) {
            val diffInit = fDecl.initExp as DifferentialExp
            equalities += "& ${fDecl.name} = ${translateExpr(diffInit.initVal)}"
        }
        val runImpl = cDecl.initBlock
        var transRet = Triple<DlStmt, Set<MethodSig>, PlaceMap>(DlSkip, emptySet(), mutableMapOf())
        if(runImpl != null) transRet = extractBlock(runImpl,false)

        val runSig = cDecl.methods.map { it.methodSig }.firstOrNull { it.name == "run" }
        if(runSig != null)
            transRet = Triple(transRet.first, transRet.second + runSig, transRet.third )

        val tactic = extractSpec(cDecl,"Tactic", default = "expandAllDefs; master", multipleAllowed = false)
        val res =
        proofObligationNew(
            "$CONTRACTVARIABLE = 1",
            transRet,
            "true",
            inv,
            "$equalities & $pre",
            "/tmp/chisel/$name",
            "init.kyx",
            emptyList(),
            tactic)
        output("Inital proof obligation result: \n$res\n", Verbosity.V)
        return res
    }

    fun proofObligationMethod(mDecl : MethodImpl) : Boolean{
        val read  = collect(AssignStmt::class.java, mDecl).filter { it.`var` is FieldUse }
        val mayCall  = collect(Call::class.java, mDecl)
        val create  = collect(NewExp::class.java, mDecl)
        val specDecl = findInterfaceDecl(mDecl.methodSig)
        val sPec =  if(specDecl == null) "true" else extractSpec(specDecl,"Ensures")
        if(read.isEmpty() && mayCall.isEmpty() && create.isEmpty() && sPec == "true"){
            output("Skipping ${mDecl.methodSig.name} because it does not write into the heap, makes no calls, creates no objects and has no Ensures specification")
            return true
        }


        val mSig = findInterfaceDecl(mDecl, mDecl.contextDecl as ClassDecl)
        val pre = "$inv & $CONTRACTVARIABLE = 1 & $TIMEVARIABLE = 0 & "+if(mSig != null){
            extractSpec(mSig,"Requires")
        } else "true"

        val init = translateGuard(extractInitial(mDecl))
        val transRet  = extractImpl(mDecl)
        val post = "$CONTRACTVARIABLE = 1 & $inv & $sPec"

        val extraFields =  collect(VarUse::class.java,mDecl).map { it.name }
        val tactic = extractSpec(mDecl,"Tactic", default = "expandAllDefs; master", multipleAllowed = false)
        val res = proofObligationNew(
            post,
            transRet,
            init,
            inv,
            pre,
            "/tmp/chisel/$name",
            "${mDecl.methodSig.name}.kyx",
            extraFields,
            tactic)
        output("Method proof obligation for ${mDecl.methodSig.name}:\n$res\n", Verbosity.V)
        return res

    }

    private fun getRegionString(connector : String = " | ") : String {
        if(ctrlRegions.isEmpty()) return "true"
        return ctrlRegions.joinToString(connector) { "($it)" }
    }

    //TODO: add check for subset from the paper
    fun proofObligationZeno(mDecl : MethodImpl) : Boolean {
        //if()//check locally Zeno checked fragment
        val mSig = findInterfaceDecl(mDecl, mDecl.contextDecl as ClassDecl)
        val pre = "$inv & $CONTRACTVARIABLE = 1 & $TIMEVARIABLE = 0 & "+if(mSig != null){
            extractSpec(mSig,"Requires")
        } else "true"

        val init = translateGuard(extractInitial(mDecl))
        val transRet  = extractImpl(mDecl)

        val extraFields =  collect(VarUse::class.java,mDecl).map { it.name }
        val tactic = extractSpec(mDecl,"Tactic", default = "expandAllDefs; master", multipleAllowed = false)
        val res = proofObligationZenoNew(
            transRet,
            init,
            inv,
            pre,
            "/tmp/chisel/$name",
            "${mDecl.methodSig.name}.kyx",
            extraFields,
            tactic)
        output("Method proof obligation for locally Zeno behavior of ${mDecl.methodSig.name}:\n$res\n", Verbosity.V)
        return res
    }


    fun proofObligationsAllZeno() : Boolean{
        var res = true
        for(mDecl in cDecl.methods){
            val next =  proofObligationZeno(mDecl)
            output("verification result for locally Zeno behavior of ${cDecl.name +"."+mDecl.methodSig.name}: $next")
            res = res && next
        }
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

    fun proofObligationZenoNew(
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
        var newpre = "$pre & $init & $inv"
        fields.forEach {
            newpre = newpre.replace("$it'","${it}der")
        }
        val paramListDer = "${(fields+extraFields).joinToString(", ") { "Real $it" }}, ${(fields+extraFields).joinToString(", ") { "Real ${it}der" }}"
        val paramListCallSubst = "${(fields+extraFields).joinToString(", ") { it }}, ${(fields+extraFields).joinToString(", ") { "${it}'" }}"

        val progDefs =
            listOf(Pair("anon", fields.filter { it != CONTRACTVARIABLE }.joinToString (";",transform = {"$it := *" })+";"),
                Pair("skip", "?true;"))


        val predDefs =
            listOf(Pair("pre", newpre))


        var prog = transRet.first.prettyPrint(2)
        for(entry in transRet.third){
            prog = prog.replace(entry.key,"([${regionFor(entry.value.first, entry.value.second)}]$inv)")
        }


        val prob =
            """
            |pre($paramListCallSubst)
            |   -> 
            |   \exists $ZENOLIMITVARIABLE ( $ZENOLIMITVARIABLE > 0 & (
            |   [
            |   ?$init;
            |   $prog
            |   $TIMEVARIABLE := 0; {$trPh, $TIMEVARIABLE' = 1 & $TIMEVARIABLE <= $ZENOLIMITVARIABLE}
            |   ]
            |   (
            |   !(${getRegionString("|")})
            |   ) ))
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

    override fun regionFor(extra : String, call : Set<MethodSig>) : String =
        when(reg) {
            RegionOption.BasicRegion -> {
                "{$trPh & true}"
            }
            RegionOption.UniformRegion -> {
                val guards = call.map { extractInitial(find(it, cDecl)) }
                val dGuards = guards.filterIsInstance<DifferentialGuard>().map { "!(" + translateGuard(it.condition) + ")" }
                val region = if (dGuards.isEmpty()) "true" else dGuards.joinToString("&")
                " $TIMEVARIABLE := 0; {$trPh, $TIMEVARIABLE' = 1 & $region & $extra}"
            }
            RegionOption.CtrlRegion -> {
                val guards = call.map { extractInitial(find(it, cDecl)) }
                val dGuards = guards.filterIsInstance<DifferentialGuard>().map { "!(" + translateGuard(it.condition) + ")" }
                var region = if (dGuards.isEmpty()) "true" else dGuards.joinToString("&")
                region = "$region & !(${getRegionString()})"
                " $TIMEVARIABLE := 0; {$trPh, $TIMEVARIABLE' = 1 & $region & $extra}"
            }
        }
}


fun<T : ASTNode<out ASTNode<*>>?> extractSpec(decl : ASTNode<T>, expectedSpec : String, default:String = "true", multipleAllowed:Boolean = true) : String {
    var ret : String = default
    for (annotation in decl.nodeAnnotations) {
        if (!annotation.type.toString().endsWith(".HybridSpec")) continue
        if (annotation.getChild(0) !is DataConstructorExp) {
            throw Exception("Could not extract any specification $expectedSpec from $decl because of the expected value")
        }
        val annotated = annotation.getChild(0) as DataConstructorExp
        if (annotated.constructor != expectedSpec) continue
        val next = (annotated.getParam(0) as StringLiteral).content
    if (!multipleAllowed) { ret = next; break }
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


fun extractImpl(mImpl: MethodImpl) : Triple<DlStmt, Set<MethodSig>, PlaceMap>{
    return extractBlock(mImpl.block,extractInitial(mImpl) != null)
}


fun extractBlock(block: Block, skipFirst : Boolean) : Triple<DlStmt, Set<MethodSig>, PlaceMap>{
    val map : PlaceMap = mutableMapOf()
    val trans = translateStmt(block, emptySet(), map, skipFirst)
    return Triple(trans.first, trans.second, map)
}

