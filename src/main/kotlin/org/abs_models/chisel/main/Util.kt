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

fun findInterfaceDecl(model: Model, methodImpl: MethodImpl, classDecl: ClassDecl) : MethodSig? {
    //for (mDecl in model.moduleDecls.filter { !it.name.startsWith("ABS.") }){
      //  for( iDecl in mDecl.decls.filterIsInstance<InterfaceDecl>()){
       for( iDecl in classDecl.implementedInterfaceUseList.map { it.decl as InterfaceDecl }){
            for( mDecl in iDecl.allMethodSigs){
                if(mDecl.matches(methodImpl.methodSig)) return mDecl
            }
        }
    //}
    return null

}