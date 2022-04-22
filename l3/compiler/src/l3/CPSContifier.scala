package l3

import l3.SymbolicCPSTreeModule._
import L3Primitive.Id

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.mutable.{ Set => MutableSet }

object CPSContifier extends (Tree => Tree) {

  def apply(tree: Tree): Tree = {
    val pt = PropIdentities.apply(tree)
    val analysis = analyze(pt)
    transform(pt, analysis)
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

  implicit class MultiMutableMapUtils[K, V](m: MutableMap[K, Set[V]]) {
    def +>=(t: (K, V)): Unit = {
      val (from, to) = t
      val s: Set[V] = m.getOrElse(from, Set[V]())
      m += (from -> (s + to))
    }
  }

  implicit class SetUtils[T](set: Set[T]) {
    def minimize(shrink: (T, T) => Option[T]): Set[T] = {
      fixedPoint(set) { s =>
        val remaining: MutableSet[T] = MutableSet()
        if (s.size <= 1)
          return s // !
        val toPartition = s.grouped(2)
        toPartition.foreach { pair =>
          pair.toList match {
            case List(f, s) =>
              shrink(f, s) match {
                case Some(merged) => remaining += merged
                case None         => remaining ++= pair
              }
            case List(s) =>
              remaining += s
          }
        }
        remaining.toSet
      }
    }
  }

  implicit class Tuple2Utils[S, T](t: (S, T)) {
    def map[V](transformer: T => V): (S, V) =
      (t._1, transformer(t._2))
  }

  private def analyze(tree: Tree): CFGraph = {
    val outEdges =
      MutableMap[CNode, Set[CNode]]().withDefault(_ => Set.empty)
    val inEdges =
      MutableMap[CNode, Set[CNode]]().withDefault(_ => Set.empty)
    val funRetCs = MutableMap[Name, Name]()
    val funBodies = MutableMap[Name, Tree]()
    val cntBodies = MutableMap[Name, Tree]()
    // If a function or continuation was seen, then it was
    // used in the program flow and cannot be removed.
    val seen = MutableSet[Name]()
    // Mutable utiliies for graph
    def withEdge(from: CNode, to: CNode): Unit = {
      outEdges +>= (from -> to); inEdges +>= (to -> from)
    }
    def usedAsValue(a: Atom): Unit = a match {
      case AtomN(n) if (funRetCs contains n) =>
        withEdge(Root, Cont(funRetCs(n)))
        seen += n
        // Assume that the function will be called
        buildGraph(funBodies(n))
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
        args map usedAsValue; doUnseen(cntBodies, tK);
        doUnseen(cntBodies, fK)
      case Halt(a) =>
        usedAsValue(a)
    }

    val _ = buildGraph(tree) // ! State
    val g = Graph(outEdges.toMap, inEdges.toMap)
    val retCs: Set[CNode] = funRetCs.values.map(Cont).toSet
    val sccs: Seq[Set[Name]] = stronglyConnectedComponents(g)
      .filter { scc =>
        // Functions with in edge of Root cannot be contified (used as value)
        scc.forall { v => !(inEdges(v) contains Root) } &&
        // Components including non-retC continuations are just wrong
        scc.forall { retCs contains _ } &&
        // The component must all return to *the same* place (i.e. static jump)
        ((scc.foldLeft(Set[CNode]()) { _ ++ inEdges(_) } &~ scc).size == 1)
      }
      .map { _.map { case Cont(v) => v } }
    CFGraph(g, funRetCs.toMap, seen.toSet, sccs)
  }

  // -----------------------------------
  // Contification transformation

  case class CFGraph(
      graph: Graph[CNode],
      funRetCs: Map[Name, Name],
      seen: Set[Name],
      sccs: Seq[Set[Name]],
      cSubst: Subst[Name] = emptySubst,
      fEnv: Map[Name, Name] = Map(),
      sccEnv: Set[Set[Fun]] = Set()
  ) {
    def uncalled(f: Name): Boolean = !(seen contains f)
    def cSub(n: Name): Name = cSubst(n)
    def withCSubst(from: Name, to: Name): CFGraph =
      copy(cSubst = cSubst + (from -> cSubst(to)))
    def withSCC(scc: Set[Fun]): CFGraph =
      copy(
        sccEnv = sccEnv + scc,
        fEnv = fEnv ++ (scc map { f => (f.name, Symbol.fresh("j")) })
      )
    def withSCCs(sccs: Seq[Set[Fun]]): CFGraph =
      sccs.foldLeft(this)(_.withSCC(_))
    def getJ(f: Name): Name = fEnv(f)
    def withKs(scc: Set[Fun]): CFGraph = {
      val sccCNode: Set[CNode] = scc map { f => Cont(f.retC) }
      val Cont(k) =
        (sccCNode.foldLeft(Set[CNode]()) {
          _ ++ graph.inEdges(_)
        } &~ sccCNode).head
      scc.foldLeft(this) { (st, f) => st.withCSubst(f.retC, k) }
    }
  }

  /** Collapse
    *
    * Attempt to collapse a set of strongly connected continuations into each
    * other. NOTE If the components are defined correctly, this is a
    * non-associative operation. Collapse, specifically attempts both directions
    * making the wrapper function associative and thus usable with reductions
    * e.g. 'minimize'
    */
  def collapse(lhs: Set[Cnt], rhs: Set[Cnt]): Option[Set[Cnt]] = {
    def collapseSCC(from: Set[Cnt], to: Set[Cnt]): Option[Set[Cnt]] = {
      val pushed: Set[Either[Cnt, Cnt]] = to.map {
        case c @ Cnt(name, args, body) =>
          pushCntDefinition(from, body) match {
            case None    => Left(c)
            case Some(b) => Right(Cnt(name, args, b))
          }
      }
      if (pushed exists { _.isRight })
        Some(pushed map {
          case Left(f)  => f
          case Right(f) => f
        })
      else None
    }
    collapseSCC(lhs, rhs).orElse(collapseSCC(rhs, lhs))
  }

  def transform(treeP: Tree, info: CFGraph): Tree = {
    def rewriteAll(t: Tree)(implicit info: CFGraph): Tree = t match {
      case LetP(name, prim, args, body) =>
        LetP(name, prim, args, rewriteAll(body))
      case LetC(cnts, body) =>
        LetC(
          cnts.map { case Cnt(name, args, body) =>
            Cnt(name, args, rewriteAll(body))
          },
          rewriteAll(body)
        )
      case LetF(funs, body) =>
        LetF(
          funs.map { case Fun(name, retC, args, body) =>
            Fun(name, retC, args, rewriteAll(body))
          },
          rewriteAll(body)
        )
      case AppF(AtomN(f), retC, args) =>
        info.fEnv.get(f) match {
          case Some(k) => AppC(info.cSubst(k), args)
          case None    => AppF(AtomN(f), info.cSubst(retC), args)
        }
      case AppC(cnt, args)       => AppC(info.cSubst(cnt), args)
      case AppF(fun, retC, args) => AppF(fun, info.cSubst(retC), args)
      case If(cond, args, thenC, elseC) =>
        If(cond, args, info.cSubst(thenC), info.cSubst(elseC))
      case Halt(arg) => Halt(arg)
    }

    def loop(tree: Tree)(implicit info: CFGraph): (CFGraph, Tree) = {
      def ret(t: Tree, s: CFGraph = info): (CFGraph, Tree) = (s, t)
      tree match {
        case LetP(name, prim, args, body) =>
          loop(body) map { b => LetP(name, prim, args, b) }
        case LetC(cnts, body) =>
          val (state, ks) = mapAccumR(info, cnts) {
            case (st, Cnt(name, args, body)) =>
              loop(body) map { b => Cnt(name, args, b) }
          }
          val fltd = ks filterNot { k => state.uncalled(k.name) }
          loop(body)(state) map { b => LetC(fltd.toSeq, b) }
        case LetF(Seq(), body) => loop(body)
        case LetF(funsP, body) =>
          // Remove all dead functions
          val funs = funsP filterNot { f => info.uncalled(f.name) }
          val retCMapped = (funs.map(_.retC) zip funs).toMap
          val (sccs: Seq[Set[Fun]], remFsNs: Set[Name]) =
            info.sccs.foldLeft((Seq[Set[Fun]](), retCMapped.keys.toSet)) {
              case ((sccs, fs), scc) =>
                if (scc.subsetOf(fs))
                  ((scc map retCMapped) +: sccs, fs &~ scc)
                else (sccs, fs)
            }
          // The remaining functions: not contifiable nor dead
          val remFsP: Seq[Fun] = (remFsNs map retCMapped).toSeq
          // We can use this new state for transforming and pushing all
          // tree nodes from here forward, as it does not define continuation
          // definitions, it will only rewrite usages which are guaranteed to
          // be in the right place.
          val state = sccs.foldLeft(info.withSCCs(sccs)) { _.withKs(_) }

          val (newS, sccsK) =
            mapAccumR(state, sccs) { (s, scc) =>
              mapAccumR(s, scc) { case (s, Fun(name, _, args, body)) =>
                val j = s.getJ(name)
                loop(body)(s) map { b => Cnt(j, args, b) }
              }
            }

          val (newState, remFs) = mapAccumR(newS, remFsP) {
            case (s, Fun(name, retC, args, body)) =>
              loop(body)(s) map { b => Fun(name, retC, args, b) }
          }

          /* A SCC usage can occur in one of three places:
           * (1) The 'body' of this LetF.
           * (2) The body of a [single] function in 'remFs'.
           * (3) The body of a [single] continuation in 'sccs'
           *     that is NOT the same scc.
           *
           * The set of mutually recursive continuations needs
           * to be pushed as far down the respective body as
           * possible.
           *
           * First, try to identify SCCS that are used in another
           * SCC. This will reduce the list of SCCS to handle.
           *
           * Second, try to identify SCCS that are used in a body
           * of 'remFs' and place them there.
           *
           * Third, the usage must be in the body of the LetF,
           * push each one down the tree there.
           *
           */

          // FIXME the merging code is wildly inefficient.

          // ASSUMPTION: an SCC cannot be collapsed into more than
          // one other SCC.
          // If it were, they would not be disjoint SCCs
          val collapsedSccs: Set[Set[Cnt]] =
            sccsK.map { _.toSet }.toSet.minimize { collapse(_, _) }
          // Push the remaining continuation definitions into the LetF node
          // which contains the functions that couldn't be contified.
          val (innerState, newBody) = loop(body)(newState)
          ret(
            collapsedSccs.foldRight(LetF(remFs.toSeq, newBody): Tree) {
              (scc, acc) =>
                pushCntDefinition(scc, acc) match {
                  case Some(good) =>
                    rewriteAll(good)(innerState)
                  case None =>
                    println(s"Failed on merging: $scc")
                    println(s"Into: $acc")
                    ???
                }
            },
            innerState
          )
        case AppF(AtomN(f), retC, args) =>
          info.fEnv.get(f) match {
            case Some(k) => ret(AppC(k, args))
            case None    => ret(AppF(AtomN(f), info.cSub(retC), args))
          }
        case AppC(cnt, args)       => ret(AppC(info.cSub(cnt), args))
        case AppF(fun, retC, args) => ret(AppF(fun, info.cSub(retC), args))
        case If(cond, args, thenC, elseC) =>
          ret(If(cond, args, info.cSub(thenC), info.cSub(elseC)))
        case Halt(arg) => ret(Halt(arg))
      }
    }

    loop(treeP)(info)._2
  }

  /** pushCntDefinition
    *
    * Given a sequence of mutually recursive continuation definitions 'cnts',
    * push this definition as far down as possible in the 'tree' body. If none
    * of the continuations is used in 'tree', the return value is NONE.
    * Otherwise, the result is Some(newTree) with the continuations pushed as
    * far down as possible.
    */
  def pushCntDefinition(cnts: Iterable[Cnt], treeP: Tree): Option[Tree] = {
    def inSet(n: Name): Boolean = cnts.exists { c => c.name == n }
    def wrap(t: Tree): Tree = LetC(cnts.toSeq, t)
    def loop(tree: Tree): Option[Tree] = tree match {
      case LetP(name, prim, args, body) =>
        pushCntDefinition(cnts, body) map { b => LetP(name, prim, args, b) }
      case LetC(conts, body) =>
        val newCnts: Seq[Either[Cnt, Cnt]] = conts.map {
          case k @ Cnt(name, args, body) =>
            pushCntDefinition(cnts, body) match {
              case None         => Left(k)
              case Some(merged) => Right(Cnt(name, args, merged))
            }
        }
        val inCntBodies = newCnts.exists(_.isRight)
        val ks = newCnts.map {
          case Left(k)  => k
          case Right(k) => k
        }
        pushCntDefinition(cnts, body) match {
          case None if !inCntBodies         => None
          case None                         => Some(LetC(ks, body))
          case Some(merged) if !inCntBodies => Some(LetC(ks, merged))
          case Some(_)                      => Some(wrap(tree))
        }
      case LetF(funs, body) =>
        val newFuns: Seq[Either[Fun, Fun]] = funs.map {
          case f @ Fun(name, retC, args, body) =>
            pushCntDefinition(cnts, body) match {
              case None         => Left(f)
              case Some(merged) => Right(Fun(name, retC, args, merged))
            }
        }
        val inFunBodies = newFuns.exists(_.isRight)
        val fs = newFuns map {
          case Left(f)  => f
          case Right(f) => f
        }
        pushCntDefinition(cnts, body) match {
          case None if !inFunBodies         => None
          case None                         => Some(LetF(fs, body))
          case Some(merged) if !inFunBodies => Some(LetF(funs, merged))
          case Some(_)                      => Some(wrap(tree))
        }
      case AppC(cnt, _) if inSet(cnt)                 => Some(wrap(tree))
      case AppF(_, retC, _) if inSet(retC)            => Some(wrap(tree))
      case If(_, _, tK, fK) if inSet(tK) || inSet(fK) => Some(wrap(tree))
      case AppC(_, _)                                 => None
      case AppF(_, _, _)                              => None
      case If(_, _, _, _)                             => None
      case Halt(_)                                    => None
    }
    loop(treeP)
  }
}
