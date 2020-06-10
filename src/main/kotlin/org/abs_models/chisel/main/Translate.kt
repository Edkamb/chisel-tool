package org.abs_models.chisel.main

import abs.frontend.ast.*

const val SKIP = "skip;"

fun isClean(stmt: Stmt?) : Boolean{
    if(stmt == null) return true
    when(stmt) {
        is AssignStmt -> {
            return false
        }
        is IfStmt -> {
            return isClean(stmt.then) && isClean(stmt.`else`)
        }
        is WhileStmt -> {
            return isClean(stmt.body)
        }
        is Block -> {
            return stmt.stmts.all { isClean(it) }
        }
        is CaseStmt -> {
            return stmt.branchs.map { it.right }.all { isClean(it) }
        }
        else -> return true
    }
}

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
        is IfStmt -> {
            return "if(${translateExpr(stmt.condition)}) {${translateStmt(stmt.then)}} else {${translateStmt(stmt.`else`)}} "
        }
        is ExpressionStmt -> {
            if(stmt is Call){
                if(stmt.callee.toString() == "this") SKIP
                else throw Exception("Translation not supported yet: $stmt")
            }
            return SKIP
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
        is MultMultExp -> return "(${translateExpr(exp.left)}/${translateExpr(exp.right)})"
        is ModMultExp -> return "(${translateExpr(exp.left)}/${translateExpr(exp.right)})"
        is SubAddExp -> return "(${translateExpr(exp.left)}-${translateExpr(exp.right)})"
        is AddAddExp -> return "(${translateExpr(exp.left)}+${translateExpr(exp.right)})"
        is LTEQExp -> return "(${translateExpr(exp.left)}<=${translateExpr(exp.right)})"
        is LTExp -> return "(${translateExpr(exp.left)}<${translateExpr(exp.right)})"
        is GTExp -> return "(${translateExpr(exp.left)}>${translateExpr(exp.right)})"
        is GTEQExp -> return "(${translateExpr(exp.left)}>=${translateExpr(exp.right)})"
        is EqExp -> return "(${translateExpr(exp.left)}==${translateExpr(exp.right)})"
        is NotEqExp -> return "(${translateExpr(exp.left)}!=${translateExpr(exp.right)})"
        is OrBoolExp -> return "(${translateExpr(exp.left)}|${translateExpr(exp.right)})"
        is AndBoolExp -> return "(${translateExpr(exp.left)}&${translateExpr(exp.right)})"
        is IntLiteral -> return "(${exp.content})"
        is FieldUse -> return "$exp"
        is VarUse -> return "$exp"
        is DiffOpExp -> return "${translateExpr(exp.getChild(0) as Exp)}'"
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
        is DurationGuard -> "t >= ${translateExpr(exp.min)}"
        is ClaimGuard -> "true"
        else -> {throw Exception("Translation not supported yet: $exp")}
    }
}


fun getCalled(stmt: Stmt?): Set<MethodSig> {
    if(stmt == null) return emptySet()
    when(stmt) {
        is AssignStmt -> {
            return if(stmt.callExpression is Call) setOf(stmt.callExpression.methodSig)
            else emptySet()
        }
        is ExpressionStmt -> {
            return if(stmt.exp is Call) setOf(stmt.callExpression.methodSig)
            else emptySet()
        }
        is IfStmt -> {
            return getCalled(stmt.then) + getCalled(stmt.`else`)
        }
        is WhileStmt -> {
            return getCalled(stmt.body)
        }
        is Block -> {
            return stmt.stmts.fold(emptySet(), { acc, nx -> acc + getCalled(nx) })
        }
        is CaseStmt -> {
            return stmt.branchs.fold(emptySet(), { acc, nx -> acc + getCalled(nx.right) })
        }
        else -> return emptySet()
    }
}

fun find(methodSig: MethodSig, classDecl: ClassDecl) : MethodImpl{
    return classDecl.methods.first { it.methodSig.matches(methodSig)}
}