package org.abs_models.chisel.main

import abs.frontend.ast.*

const val SKIP = "skip;"

fun translateStmt(stmt: Stmt?) : String{
    if(stmt == null) return SKIP
    when(stmt){
        is AssignStmt -> {
            when(stmt.getChild(2)){
                is PureExp ->
                    return stmt.`var`.toString() + " := "+ translateExpr(stmt.getChild(2) as PureExp)+";"
                else -> {throw Exception("Translation not supported yet : ${stmt.getChild(2)}")}
            }
        }
        is ReturnStmt -> {
            return "$RESULTVARIABLE := ${translateExpr(stmt.retExp)};"
        }
        is IfStmt -> {
            return "if(${translateExpr(stmt.condition)}) {${translateStmt(stmt.then)}} else {${translateStmt(stmt.`else`)}} "
        }
        is ExpressionStmt -> {
            return if(stmt.exp is PureExp) SKIP
                   else translateExpr(stmt.exp)
        }
        is VarDeclStmt -> {
            return if(stmt.varDecl.initExp is PureExp) stmt.varDecl.name+" := "+translateExpr(stmt.varDecl.initExp as Exp)+";"
            else "{"+translateExpr(stmt.varDecl.initExp as Exp) + "; "+stmt.varDecl.name+" := *;}"
        }
        is Block -> {
            return stmt.stmts.joinToString(" ") { translateStmt(it) }
        }
        else -> {throw Exception("Translation not supported yet: $stmt")}
    }
}

fun translateExpr(exp: Exp) : String{
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
        is DiffOpExp -> return "${translateExpr(exp.getChild(0) as Exp)}'"
        is DifferentialExp -> return translateExpr(exp.left)+"="+translateExpr(exp.right)
        is AsyncCall -> {
            val mSig = exp.methodSig
            val mSsig = findInterfaceDecl(mSig.contextMethod, mSig.contextDecl as ClassDecl) ?: return SKIP
            var spec = extractSpec(mSsig,"Requires")

            for(i in 0 until exp.numParam)
                spec = spec.replace(mSsig.getParam(i).name, translateExpr(exp.getParam(i)))
            return "{{?($spec);skip;} ++ {?(!$spec);$CONTRACTVARIABLE := 0;}}"
        }
        is NewExp -> {
            val cDecl = findClass(exp.model, exp.className)
            var spec = extractSpec(cDecl,"Requires")
            for(i in 0 until cDecl.numParam)
                spec = spec.replace(cDecl.getParam(i).name, translateExpr(exp.getParam(i)))
            return "{{?($spec);skip;} ++ {?(!$spec);$CONTRACTVARIABLE := 0;}}"
        }
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