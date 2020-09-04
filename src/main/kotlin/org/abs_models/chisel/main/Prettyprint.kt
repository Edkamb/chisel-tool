package org.abs_models.chisel.main

const val PLACE = "\t"

interface DlStmt{
    fun prettyPrint(level : Int = 0) : String
}
object DlSkip : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"skip;"
}
object DlAnon : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"anon;"
}

@Suppress("unused")
data class DlCont(val ode : String, val domain : String) : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"{$ode & $domain};"
}
data class DlAssign(val target : String, val term : String) : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"$target := $term;"
}
data class DlNonDetAssign(val target : String) : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"$target := *;"
}
data class DlCheck(val target : String) : DlStmt {
    override fun prettyPrint(level : Int ) : String {
     return   PLACE.repeat(level) + "?$target;"
    }
}

@Suppress("unused")
data class DlStar(val inner : DlStmt) : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"(\n"+
        inner.prettyPrint(level+1)+"\n"+
        PLACE.repeat(level)+")*"
}
data class DlSeq(val first : DlStmt, val second : DlStmt) : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        first.prettyPrint(level) + "\n"+
        second.prettyPrint(level)
}
data class DlOr(val first : DlStmt, val second : DlStmt) : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"{\n"+
        first.prettyPrint(level+1) + "\n"+
        PLACE.repeat(level)+"} ++ {"+"\n"+
        second.prettyPrint(level+1)+ "\n"+
        PLACE.repeat(level)+"}"
}
data class DlBlock(val inner : DlStmt) : DlStmt {
    override fun prettyPrint(level : Int ) : String =
        PLACE.repeat(level)+"{\n"+
        inner.prettyPrint(level+1)+"\n"+
        PLACE.repeat(level)+"}"
}