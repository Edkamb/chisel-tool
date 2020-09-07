package org.abs_models.chisel.main

import abs.frontend.ast.*

fun collect(
    node: ASTNode<out ASTNode<*>>,
    found: MutableSet<ASTNode<out ASTNode<*>>>,
    filter: (ASTNode<out ASTNode<*>>) -> Boolean) {
    if(filter(node)) found.add(node)
    for ( sub in node.astChildren() ) collect(sub, found, filter)
}

inline fun <reified T: ASTNode<out ASTNode<*>>> collect(clazz : Class<T>, node: ASTNode<out ASTNode<*>>) : List<T> {
    val read : MutableSet<ASTNode<out ASTNode<*>>> = mutableSetOf()
    collect(node, read) { clazz.isInstance(it)}
    return read.filterIsInstance(clazz) // the filter is there to make the type checker happy
}

fun findClass(model: Model, inName : String) : ClassDecl {
    for (mDecl in model.moduleDecls)
        for( cDecl in mDecl.decls)
            if(cDecl is ClassDecl && cDecl.name == inName) return cDecl
    throw Exception("cannot find class $inName to extract its creation condition")
}

fun findInterfaceDecl(methodSig: MethodSig) : MethodSig? {
    if(methodSig.contextMethod == null || methodSig.contextDecl == null || methodSig.contextDecl !is ClassDecl) return null
    val classDecl = methodSig.contextDecl as ClassDecl
    return findInterfaceDecl(methodSig.contextMethod , classDecl)
}

fun findInterfaceDecl(methodImpl: MethodImpl, classDecl: ClassDecl) : MethodSig? {
       for( iDecl in classDecl.implementedInterfaceUseList.map { it.decl as InterfaceDecl }){
            for( mDecl in iDecl.allMethodSigs){
                if(mDecl.matches(methodImpl.methodSig)) return mDecl
            }
        }
    return null
}

fun extractBlock(block: Block, skipFirst : Boolean, inv : String = "true") : Triple<DlStmt, Set<MethodSig>, PlaceMap>{
    val map : PlaceMap = mutableMapOf()
    val trans = translateStmt(block, emptySet(), map, skipFirst, inv)
    return Triple(trans.first, trans.second, map)
}

fun extractImpl(mImpl: MethodImpl, inv: String = "true") : Triple<DlStmt, Set<MethodSig>, PlaceMap>{
    return extractBlock(
        mImpl.block,
        extractInitial(mImpl) != null,
        inv
    )
}

fun extractInitial(mImpl : MethodImpl) : Guard?{
    val lead = mImpl.block.getStmt(0)
    return if(lead is AwaitStmt && (lead.guard is DifferentialGuard || lead.guard is DurationGuard)){
        lead.guard
    }else null
}

fun extractPhysical(physicalImpl: PhysicalImpl) : String{
    return physicalImpl.fields.joinToString(", ") {
        val exp = it.initExp as DifferentialExp
        if(exp.left is DiffOpExp){
            translateExpr(exp.left) + " =" + translateExpr(
                exp.right
            )
        } else throw Exception("Only ODEs are supported for translation to KeYmaera X, LHS found: ${exp.left}")
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