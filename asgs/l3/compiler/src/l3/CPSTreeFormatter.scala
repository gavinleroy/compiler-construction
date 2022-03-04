package l3

import org.typelevel.paiges.Doc

class CPSTreeFormatter[T <: CPSTreeModule](treeModule: T)
    extends Formatter[T#Tree] {
  import Formatter.par, treeModule._

  def toDoc(tree: T#Tree): Doc = {
    def pullLets(tree: T#Tree): (Seq[(T#Name, Doc)], Doc) = tree match {
      case LetP(name, prim, args, body) =>
        val (bdgs, bodyDoc) = pullLets(body)
        val pDoc = par(1, Doc.text(s"@$prim") +: (args map Doc.str))
        ((name, pDoc) +: bdgs, bodyDoc)
      case LetC(cnts, body) =>
        val (bdgs, bodyDoc) = pullLets(body)
        def toBdg(c: Cnt): (T#Name, Doc) =
          (c.name,
           par("cnt", 2, par(1, c.args map Doc.str), toDoc(c.body)))
        ((cnts map toBdg) ++ bdgs, bodyDoc)
      case LetF(funs, body) =>
        val (bdgs, bodyDoc) = pullLets(body)
        def toBdg(f: Fun): (T#Name, Doc) =
          (f.name,
           par("fun", 2, par(1, (f.retC +: f.args) map Doc.str), toDoc(f.body)))
        ((funs map toBdg) ++ bdgs, bodyDoc)
      case other =>
        (Seq(), toDoc(other))
    }

    (tree: @unchecked) match {
      case LetP(_, _, _, _) | LetC(_, _) | LetF(_, _) =>
        val (bdgs, bodyDoc) = pullLets(tree)
        val tag = if (bdgs.length > 1) "let*" else "let"
        val bdgsDoc = par(1, bdgs map (b => par(1, Doc.str(b._1), b._2)))
        par(tag, 2, bdgsDoc, bodyDoc)
      case AppF(fun, retC, args) =>
        par(1, (fun +: retC +: args) map Doc.str)
      case AppC(cont, args) =>
        par(1, (cont +: args) map Doc.str)
      case If(p, args, thenC, elseC) =>
        val pDoc = par(1, Doc.text(s"@$p") +: (args map Doc.str))
        par("if", 2, pDoc, Doc.str(thenC), Doc.str(elseC))
      case Halt(arg) =>
        par("halt", 2, Doc.str(arg))
    }
  }
}

object CPSTreeFormatter {
  implicit object SymbolicCPSTreeFormatter
      extends CPSTreeFormatter(SymbolicCPSTreeModule)
}
