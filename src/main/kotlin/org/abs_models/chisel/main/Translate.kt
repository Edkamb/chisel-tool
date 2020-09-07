package org.abs_models.chisel.main

import abs.frontend.ast.*

typealias PlaceMap = MutableMap<String, Triple<String, Set<MethodSig>, Boolean>>


fun translateStmt(stmt: Stmt?,
                  called: Set<MethodSig> = emptySet(),
                  placeholders: PlaceMap,
                  skipFirst : Boolean = false,
                  inv : String = "true")
        : Pair<DlStmt,Set<MethodSig>>{
    if(stmt == null) return Pair(DlSkip, called)
    when(stmt){
        is AssignStmt -> {
            return when(stmt.getChild(2)){
                is PureExp -> Pair(DlAssign(stmt.`var`.toString(),translateExpr(stmt.getChild(2) as PureExp))
                                 , called)
                else -> {
                    val inner = translateSideExpr(stmt.getChild(2) as EffExp, placeholders, inv)
                    val innerSet: Set<MethodSig> = if(inner.second != null) setOf(inner.second!!) else emptySet()
                    Pair(DlSeq(inner.first, DlNonDetAssign(stmt.`var`.toString())), called + innerSet)
                }
            }
        }
        is ReturnStmt -> {
            return  Pair(DlAssign(RESULTVARIABLE, translateExpr(stmt.retExp as PureExp)), called)
        }
        is IfStmt -> {
            val left = translateStmt(stmt.then, called, placeholders, skipFirst, inv)
            val right = translateStmt(stmt.`else`, called, placeholders, skipFirst, inv)
            val dlRet =
                DlBlock(DlOr(DlSeq(DlCheck(translateExpr(stmt.condition)),left.first)
                           , DlSeq(DlCheck("(!"+translateExpr(stmt.condition)+")"),right.first)))
            return Pair(dlRet ,left.second.intersect(right.second))
        }
        is ExpressionStmt -> {
            return if(stmt.exp is PureExp) Pair(DlSkip,called)
                   else {
                val inner = translateSideExpr(stmt.exp as EffExp, placeholders, inv)
                val innerSet: Set<MethodSig> = if(inner.second != null) setOf(inner.second!!) else emptySet()
                return Pair(inner.first, called + innerSet)
            }
        }
        is VarDeclStmt -> {
            return if(stmt.varDecl.initExp is PureExp) Pair(DlAssign(stmt.varDecl.name,translateExpr(stmt.varDecl.initExp as PureExp)),called)
            else{
                val inner = translateSideExpr(stmt.varDecl.initExp as EffExp, placeholders, inv)
                val innerSet: Set<MethodSig> = if(inner.second != null) setOf(inner.second!!) else emptySet()
                return Pair(DlSeq(inner.first,DlNonDetAssign(stmt.varDecl.name)), called + innerSet)
            }
        }
        is Block -> {
            val targetList = stmt.stmtsNoTransform.copy()
            if(skipFirst) targetList.removeChild(0)
            return targetList.fold(Pair(DlSkip as DlStmt,called), {
                acc, nx
                ->
                val inner = translateStmt(nx, acc.second, placeholders, skipFirst, inv)
                Pair(DlSeq(acc.first, inner.first),inner.second)
            })
        }
        is AwaitStmt -> {
            if(stmt.guard is DurationGuard) throw Exception("Translation not supported yet: $stmt")
            val trans = translateGuard( stmt.guard)
            val myName = getNewPlaceholderName()
            placeholders[myName] = Triple(trans, called, false)

            val dlRet = DlBlock(DlOr(
                  DlSeq(DlSeq(DlCheck(myName),DlAnon),DlCheck("($trans & $inv)"))
                , DlSeq(DlSeq(DlCheck("(!$myName)"),DlAnon),
                        DlSeq(DlAssign(CONTRACTVARIABLE,"0"),DlCheck(trans)))
            ))


            return Pair(dlRet, emptySet())
       }
        is DurationStmt -> { //todo: add me...
            throw Exception("Translation not supported yet: $stmt")
        }
        else -> {throw Exception("Translation not supported yet: $stmt")}
    }
}

fun translateSideExpr(exp : EffExp,
                      placeholders: PlaceMap,
                      inv : String = "true") : Pair<DlStmt,MethodSig?> {
    when (exp) {
        is AsyncCall -> {
            val mSig = exp.methodSig

            //the following does not check the precondition if there is none
            val mSigOuter = findInterfaceDecl(mSig)
                ?: return if(exp.callee is ThisExp) Pair(DlSkip,mSig) else Pair(DlSkip,null)
            var spec = extractSpec(mSigOuter, "Requires")

            for (i in 0 until exp.numParam)
                spec = spec.replace(mSigOuter.getParam(i).name, translateExpr(exp.getParam(i)))
            val dlRet =
                DlBlock(DlOr(DlSeq(DlCheck(spec),
                                   DlSkip),
                             DlSeq(DlCheck("(!$spec)"),
                                   DlAssign(CONTRACTVARIABLE, "0"))))
            return if(exp.callee is ThisExp) Pair(dlRet,mSig) else Pair(dlRet,null)
        }
        is NewExp -> {
            val cDecl = findClass(exp.model, exp.className)
            var spec = extractSpec(cDecl, "Requires")
            for (i in 0 until cDecl.numParam)
                spec = spec.replace(cDecl.getParam(i).name, translateExpr(exp.getParam(i)))
            val dlRet =
                DlBlock(DlOr(DlSeq(DlCheck(spec),
                    DlSkip),
                    DlSeq(DlCheck("(!$spec)"),
                        DlAssign(CONTRACTVARIABLE, "0"))))
            return Pair(dlRet,null)
        }
        is GetExp -> {
            val myName = getNewPlaceholderName()
            placeholders[myName] = Triple("true", emptySet(), true)

            val dlRet = DlBlock(DlOr(
                DlSeq(DlSeq(DlCheck(myName),DlAnon),DlCheck(inv))
                , DlSeq(DlSeq(DlCheck("(!$myName)"),DlAnon),
                    DlAssign(CONTRACTVARIABLE,"0"))
            ))
            return Pair(dlRet,null)
        }
        else -> {
            throw Exception("Translation not supported yet: $exp")
        }
    }
}

fun translateExpr(exp: PureExp) : String{
    when(exp) {
        is DivMultExp -> return "(${translateExpr(exp.left)}/${translateExpr(exp.right)})"
        is MultMultExp -> return "(${translateExpr(exp.left)}*${translateExpr(exp.right)})"
        is ModMultExp -> return "(${translateExpr(exp.left)}%${translateExpr(exp.right)})"
        is SubAddExp -> return "(${translateExpr(exp.left)}-${translateExpr(exp.right)})"
        is AddAddExp -> return "(${translateExpr(exp.left)}+${translateExpr(exp.right)})"
        is LTEQExp -> return "(${translateExpr(exp.left)}<=${translateExpr(exp.right)})"
        is LTExp -> return "(${translateExpr(exp.left)}<${translateExpr(exp.right)})"
        is GTExp -> return "(${translateExpr(exp.left)}>${translateExpr(exp.right)})"
        is GTEQExp -> return "(${translateExpr(exp.left)}>=${translateExpr(exp.right)})"
        is EqExp -> return "(${translateExpr(exp.left)}=${translateExpr(exp.right)})"
        is NotEqExp -> return "(!${translateExpr(exp.left)}=${translateExpr(exp.right)})"
        is OrBoolExp -> return "(${translateExpr(exp.left)}|${translateExpr(exp.right)})"
        is AndBoolExp -> return "(${translateExpr(exp.left)}&${translateExpr(exp.right)})"
        is IntLiteral -> return "(${exp.content})"
        is MinusExp -> return "(-${translateExpr(exp.operand)})"
        is FieldUse -> return "$exp"
        is VarUse -> return "$exp"
        is DiffOpExp -> return "${translateExpr(exp.getChild(0) as PureExp)}'"
        is DifferentialExp -> return translateExpr(exp.left)+"="+translateExpr(exp.right)
        else -> {throw Exception("Translation not supported yet: $exp")}
    }
}


fun translateGuard(exp: Guard?) : String{
    if(exp == null) return "true"
    return when(exp){
        is DifferentialGuard -> translateGuard(exp.condition)
        is ExpGuard -> translateExpr(exp.pureExp)
        is AndGuard -> "(${translateGuard(exp.left)}) & (${translateGuard(exp.right)})"
        is OrGuard -> "(${translateGuard(exp.left)}) | (${translateGuard(exp.right)})"
        is DurationGuard -> "$TIMEVARIABLE >= ${translateExpr(exp.min)}"
        is ClaimGuard -> "true"
        else -> {throw Exception("Translation not supported yet: $exp")}
    }
}

fun find(methodSig: MethodSig, classDecl: ClassDecl) : MethodImpl{
    return classDecl.methods.first { it.methodSig.matches(methodSig)}
}

private var counter = 0
private fun getNewPlaceholderName() : String = "#PLACE${counter++}"