package l3

import l3.SymbolicCPSTreeModule._
import L3Primitive.Id

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.mutable.{ Set => MutableSet }

object CPSContifier extends (Tree => Tree) {

  type MultiMap[K, V] = Map[K, Set[V]]

  def apply(tree: Tree): Tree = {
    val pt = PropIdentities.apply(tree)
    val analysis = analyze(pt)
    transform(pt)(analysis)
  }

  // -----------------------------------
  // Pre-contification rewrites
  // NOTE this includes id propogation
  // to make contifaction effecive.

  private case class State(
      aSubst: Subst[Atom] = emptySubst
  ) {
    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Name, to: Atom): State =
      withASubst(AtomN(from), to)
    def withASubst(from: Name, to: Literal): State =
      withASubst(from, AtomL(to))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from.map(AtomN) zip to.map(aSubst)))
  }

  object PropIdentities extends (Tree => Tree) {
    val identity: ValuePrimitive = Id

    def apply(tree: Tree): Tree =
      transform(tree, State())

    private def transform(tree: Tree, s: State): Tree = tree match {
      case LetP(name, id, Seq(a), body) if id == identity =>
        transform(body, s.withASubst(name, a))
      case LetP(name, prim, args, body) =>
        LetP(name, prim, args map s.aSubst, transform(body, s))
      case LetC(cnts, body) =>
        LetC(
          cnts map { case Cnt(name, args, body) =>
            Cnt(name, args, transform(body, s))
          },
          transform(body, s)
        )
      case LetF(funs, body) =>
        LetF(
          funs map { case Fun(name, retC, args, body) =>
            Fun(name, retC, args, transform(body, s))
          },
          transform(body, s)
        )
      case AppC(cnt, args) =>
        AppC(cnt, args map s.aSubst)
      case AppF(fun, retC, args) =>
        AppF(s.aSubst(fun), retC, args map s.aSubst)
      case If(cnd, args, tK, fK) =>
        If(cnd, args map s.aSubst, tK, fK)
      case Halt(a) =>
        Halt(s.aSubst(a))
    }
  }

  // -----------------------------------
  // Contification analysis

  sealed trait CNode
  case class Root() extends CNode
  case class Cont(k: Name) extends CNode
  case class Func(f: Name) extends CNode

  case class CFGraph(
      outEdges: MultiMap[CNode, CNode],
      inEdges: MultiMap[CNode, CNode],
      funRetCs: Map[Name, Name],
      // TODO strongly connected components
      cSubst: Subst[Name] = emptySubst,
      fEnv: Map[Name, Fun] = Map()
  ) {
    def used(f: Name): Boolean =
      (inEdges contains Cont(funRetCs(f)))
    def contRewritable(f: Name): Boolean =
      inEdges.getOrElse(Cont(funRetCs(f)), Set()).size == 1
    def withFun(fun: Fun): CFGraph =
      copy(fEnv = fEnv + (fun.name -> fun))
    def withFuns(funs: Seq[Fun]): CFGraph =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))
  }

  private def analyze(tree: Tree): CFGraph = {
    val outEdges =
      MutableMap[CNode, Set[CNode]]().withDefault(_ => Set[CNode]())
    val inEdges =
      MutableMap[CNode, Set[CNode]]().withDefault(_ => Set[CNode]())
    val funRetCs = MutableMap[Name, Name]()
    val funBodies = MutableMap[Name, Tree]()
    val cntBodies = MutableMap[Name, Tree]()
    val seen = MutableSet[Name]()

    // Mutable utiliies for graph

    def withEdge(from: CNode, to: CNode): Unit = {
      val setOut = outEdges(from)
      val setIn = inEdges(to)
      outEdges += (from -> (setOut + to))
      inEdges += (to -> (setIn + from))
    }
    def usedAsValue(a: Atom): Unit = a match {
      case AtomN(n) =>
        if (funRetCs contains n)
          withEdge(Root(), Cont(funRetCs(n)))
      case AtomL(_) => ()
    }
    def doUnseen(mapper: MutableMap[Name, Tree], n: Name): Unit =
      if (!(seen contains n)) {
        seen += n
        buildGraph(mapper(n))
      }

    // Logic for Tree -> DomTree

    def buildGraph(tree: Tree): Unit = tree match {
      case LetP(_, _, args, body) =>
        args map usedAsValue; buildGraph(body)
      case LetC(cnts, body) =>
        cnts map { case Cnt(name, _, body) =>
          cntBodies += (name -> body); withEdge(Root(), Cont(name))
        }
        buildGraph(body)
      case LetF(funs, body) =>
        funs map { case Fun(name, retC, _, body) =>
          funRetCs += (name -> retC); funBodies += (name -> body)
        }
        buildGraph(body)
      case AppC(cnt, args) =>
        args map usedAsValue;
        if (cntBodies contains cnt)
          doUnseen(cntBodies, cnt)
      case AppF(AtomN(f), retC, args) =>
        args map usedAsValue;
        if (funRetCs contains f) { // Non-free functions
          withEdge(Cont(retC), Cont(funRetCs(f)));
          doUnseen(funBodies, f)
        }
      case AppF(_, _, args) =>
        args map usedAsValue
      case If(_, args, tK, fK) =>
        args map usedAsValue;
        doUnseen(cntBodies, tK);
        doUnseen(cntBodies, fK)
      case Halt(a) =>
        usedAsValue(a)
    }
    buildGraph(tree) // ! State
    // TODO strongly connected components
    CFGraph(outEdges.toMap, inEdges.toMap, funRetCs.toMap)
  }

  // -----------------------------------
  // Contification transformation

  def transform(tree: Tree)(implicit info: CFGraph): Tree = tree match {
    case LetP(name, prim, args, body) =>
      LetP(name, prim, args, transform(body))
    case LetC(cnts, body) =>
      LetC(cnts, transform(body))
    case LetF(funs, body) =>
      // TODO partition into strongly connected components
      val fs = funs.foldRight((funs.empty)) {
        case (f @ Fun(name, retC, args, body), acc) =>
          if (!info.used(name)) {
            acc // remove dead functions
          } else if (info.contRewritable(name)) {
            // Rewrite simply contifiable funs
            println(s"$name is contRewritable")
            f +: acc
          } else f +: acc
      }
      LetF(fs, transform(body))
    case AppC(cnt, args) =>
      AppC(cnt, args)
    // NOTE a use of a contifiable function will always be
    // an AppF, because if it's used as a value then it isn't
    // contifiable. At the first use of a function, introduce
    // the Cont definition and rewrite the terms inside.
    case AppF(fun, retC, args) =>
      AppF(fun, retC, args)
    case If(cond, args, thenC, elseC) =>
      If(cond, args, thenC, elseC)
    case Halt(arg) =>
      Halt(arg)
  }
}
