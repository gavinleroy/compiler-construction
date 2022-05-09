package l3

import l3.SymbolicCPSTreeModuleLow._
import l3.{ CPSValuePrimitive => CPS }

object CPSConstantNamer extends (LetF => LetF) {
  def apply(prog: LetF): LetF =
    LetF(prog.funs map (f => Fun(f.name, f.retC, f.args, rewrite(f.body))),
         rewrite(prog.body))

  private def rewrite(tree: Tree, litSubst: Subst[Atom] = emptySubst): Tree = {
    val newLitSubst = atomsFor(tree)
      .removedAll(litSubst.keySet)
      .collect { case a @ AtomL(l) if ! fitsInNUnsignedBits(5)(l) => a }
      .map(a => a -> AtomN(Symbol.fresh(s"c$a")))
      .toMap
    val fullLitSubst = litSubst ++ newLitSubst

    val tree1 = tree match {
      case LetP(name, prim, args, body) =>
        LetP(name, prim, args map fullLitSubst, rewrite(body, fullLitSubst))
      case LetC(cnts, body) =>
        LetC(cnts.map(c => Cnt(c.name, c.args, rewrite(c.body, fullLitSubst))),
             rewrite(body, fullLitSubst))
      case AppC(cnt, args) =>
        AppC(cnt, args map fullLitSubst)
      case AppF(fun, retC, args) =>
        AppF(fullLitSubst(fun), retC, args map fullLitSubst)
      case If(cond, args, thenC, elseC) =>
        If(cond, args map fullLitSubst, thenC, elseC)
      case Halt(arg) =>
        Halt(fullLitSubst(arg))
    }

    newLitSubst.toSeq
      .sortBy { case (AtomL(l), _) => l }
      .foldRight(tree1){ case ((l, AtomN(n)), t) => LetP(n, CPS.Id, Seq(l), t) }
  }

  private def atomsFor(tree: Tree): Set[Atom] = tree match {
    case LetC(cnts, body) =>
      (body +: (cnts map (_.body)))
        .flatMap(allAtoms(_).toSeq)
        .groupBy(identity)
        .filter(_._2.length > 1)
        .keySet
    case other =>
      ownAtoms(other)
  }

  private def ownAtoms(tree: Tree): Set[Atom] = tree match {
    case LetP(_, _, args, _) =>
      args.toSet
    case LetC(_, _) =>
      Set.empty
    case AppC(_, args) =>
      args.toSet
    case AppF(fun, _, args) =>
      Set(fun) ++ args.toSet
    case If(_, args, _, _) =>
      args.toSet
    case Halt(a) =>
      Set(a)
  }

  private def descendentAtoms(tree: Tree): Set[Atom] = tree match {
    case LetP(_, _, _, body) =>
      allAtoms(body)
    case LetC(cnts, body) =>
      allAtoms(body) ++ cnts.flatMap(c => allAtoms(c.body))
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) =>
      Set.empty
  }

  private def allAtoms(tree: Tree): Set[Atom] =
    ownAtoms(tree) ++ descendentAtoms(tree)
}
