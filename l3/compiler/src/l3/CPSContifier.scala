package l3

import l3.SymbolicCPSTreeModule._
import L3Primitive.Id

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.mutable.{ Set => MutableSet }

object CPSContifier extends (Tree => Tree) {

  def apply(tree: Tree): Tree = {
    val pt = PropIdentities.apply(tree)
    val analysis = analyze(pt)
    transform(pt)(analysis)
  }

  // -----------------------------------
  // Pre-contification rewrites
  //
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
  case object Root extends CNode
  case class Cont(k: Name) extends CNode

  private def analyze(tree: Tree): CFGraph = {
    val outEdges =
      MutableMap[CNode, Set[CNode]]().withDefault(_ => Set.empty)
    val inEdges =
      MutableMap[CNode, Set[CNode]]().withDefault(_ => Set.empty)
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
      case AtomN(n) if (funRetCs contains n) =>
        // Assume that the function will be called
        withEdge(Root, Cont(funRetCs(n))); buildGraph(funBodies(n))
      case _ => ()
    }
    def doUnseen(mapper: MutableMap[Name, Tree], n: Name): Unit =
      if ((mapper contains n) && !(seen contains n)) {
        seen += n; buildGraph(mapper(n))
      }

    def buildGraph(tree: Tree): Unit = tree match {
      case LetP(_, _, args, body) =>
        args foreach usedAsValue; buildGraph(body)
      case LetC(cnts, body) =>
        cnts foreach { case Cnt(name, _, body) =>
          cntBodies += (name -> body); withEdge(Root, Cont(name))
        }
        buildGraph(body)
      case LetF(funs, body) =>
        funs foreach { case Fun(name, retC, _, body) =>
          funRetCs += (name -> retC); funBodies += (name -> body)
        }
        buildGraph(body)
      case AppC(cnt, args) =>
        args foreach usedAsValue; doUnseen(cntBodies, cnt)
      case AppF(AtomN(f), retC, args) =>
        if (funRetCs contains f)
          withEdge(Cont(retC), Cont(funRetCs(f)))
        args map usedAsValue; doUnseen(funBodies, f); doUnseen(cntBodies, retC)
      case AppF(_, _, args) =>
        args map usedAsValue
      case If(_, args, tK, fK) =>
        args map usedAsValue; doUnseen(cntBodies, tK); doUnseen(cntBodies, fK)
      case Halt(a) =>
        usedAsValue(a)
    }

    buildGraph(tree) // ! State
    val g = Graph(outEdges.toMap, inEdges.toMap)

    val sccs = stronglyConnectedComponents(g)
    // TODO filter out single sets
    // TODO filter out sets that contain non-functions
    // TODO Store in the CFGraph state

    // println(s"Graph:\n ${g.outEdges}")
    // println()
    // println(s"Strongly Connected Components:\n $sccs")
    // println()
    CFGraph(g, funRetCs.toMap)
  }

  // -----------------------------------
  // Contification transformation

  case class CFGraph(
      graph: Graph[CNode],
      funRetCs: Map[Name, Name],
      // TODO strongly connected components
      cSubst: Subst[Name] = emptySubst,
      fEnv: Map[Name, (Fun, Name)] = Map()
  ) {
    def used(f: Name): Boolean = // FIXME
      (graph.inEdges contains Cont(funRetCs(f)))
    def contRewritable(f: Name): Boolean = {
      val k = Cont(funRetCs(f))
      graph.inEdges.get(k) match {
        case Some(s) =>
          (s.size == 1) &&
            (s.head != Root) &&
            (graph.outEdges(s.head) == Set(k))
        case _ =>
          false
      }
    }
    def withCSubst(from: Name, to: Name): CFGraph =
      copy(cSubst = cSubst + (from -> cSubst(to)))
    def withFun(fun: Fun): CFGraph =
      copy(fEnv = fEnv + (fun.name -> (fun, Symbol.fresh("j"))))
    def withFuns(funs: Seq[Fun]): CFGraph =
      copy(fEnv =
        fEnv ++ (funs.map(_.name) zip funs.map((_, Symbol.fresh("j"))))
      )
    def getJ(f: Name): Name = fEnv(f)._2
    def getContK(f: Name): Name = { // NOTE must be contRewritable?
      val Cont(k) = graph.inEdges(Cont(funRetCs(f))).head
      k
    }
  }

  def transform(tree: Tree)(implicit info: CFGraph): Tree = tree match {
    case LetP(name, prim, args, body) =>
      LetP(name, prim, args, transform(body))
    case LetC(cnts, body) =>
      LetC(cnts, transform(body))
    case LetF(funs, body) =>
      // TODO partition into strongly connected components
      val (fs, ks) = funs.foldRight((funs.empty, funs.empty)) {
        case (f @ Fun(name, retC, args, body), (accf, acck)) =>
          if (!info.used(name)) {
            (accf, acck) // remove dead functions
          } else if (false && info.contRewritable(name)) {
            // Rewrite simply contifiable funs
            println(s"$name is contRewritable")
            (accf, f +: acck)
          } else (f +: accf, acck)
      }
      // build up the new state
      val state = info.withFuns(ks)
      LetF( // FIXME this naive rewrite doesn't push the k to minimal context D
        fs,
        ks.foldRight(transform(body)(state)) {
          case (Fun(name, k0, args, body), inner) =>
            val j = state.getJ(name)
            val k = state.getContK(name)
            LetC(
              Seq(Cnt(j, args, transform(body)(state.withCSubst(k0, k)))),
              inner
            )
        }
      )
    case AppC(cnt, args) =>
      AppC(info.cSubst(cnt), args)
    case AppF(AtomN(f), retC, args) =>
      info.fEnv.get(f) match {
        case Some((_, k)) =>
          AppC(k, args)
        case None =>
          AppF(AtomN(f), retC, args)
      }
    case AppF(fun, retC, args) =>
      AppF(fun, retC, args)

    // FORK
    case If(cond, args, thenC, elseC) =>
      If(cond, args, thenC, elseC)

    case Halt(arg) =>
      Halt(arg)
  }
}
