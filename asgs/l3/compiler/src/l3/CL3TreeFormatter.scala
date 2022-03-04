package l3

import org.typelevel.paiges.Doc

class CL3TreeFormatter[T <: CL3TreeModule](treeModule: T)
    extends Formatter[T#Tree] {
  import Formatter.par, treeModule._

  def toDoc(tree: T#Tree): Doc = (tree: @unchecked) match {
    case Let(bdgs, body) =>
      val bdgsDoc =
        par(1, bdgs map { case (n, v) => par(1, Doc.str(n), toDoc(v)) })
      par("let", 2, bdgsDoc, toDoc(body))
    case LetRec(funs, body) =>
      def funToDoc(fun: T#Fun): Doc =
        (Doc.str(fun.name)
           / par("fun", 2, par(1, fun.args map Doc.str), toDoc(fun.body)))
      val funsDoc = par(1, funs map { f => par(1, funToDoc(f)) })
      par("letrec", 2, funsDoc, toDoc(body))
    case If(c, t, e) =>
      par("if", 2, toDoc(c), toDoc(t), toDoc(e))
    case App(fun, args) =>
      par(1, (fun +: args) map toDoc)
    case Halt(arg) =>
      par("halt", 2, toDoc(arg))
    case Prim(prim, args) =>
      par(1, Doc.text(s"@$prim") +: (args map toDoc))
    case Ident(name) =>
      Doc.str(name)
    case Lit(l) =>
      Doc.str(l)
  }
}

object CL3TreeFormatter {
  implicit object NominalCL3TreeFormatter
      extends CL3TreeFormatter(NominalCL3TreeModule)
  implicit object SymbolicCL3TreeFormatter
      extends CL3TreeFormatter(SymbolicCL3TreeModule)
}
