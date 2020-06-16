package org.abs_models.chisel.main

import abs.frontend.ast.ASTNode

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
