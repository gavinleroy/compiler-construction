package object l3 {
  type TerminalPhaseResult = Either[String, (Int, Option[String])]

  type L3BlockTag = Int
  type L3Char = Int

  // A 32-bit integer (which could contain a pointer, a tagged value,
  // or an untagged value).
  type Bits32 = Int

  val L3_INT_BITS = java.lang.Integer.SIZE - 1

  // Bit twiddling
  def bitsToIntMSBF(bits: Int*): Int =
    bits.foldLeft(0) { (v, b) => (v << 1) | b }

  def fitsInNSignedBits(bits: Int)(value: Int): Boolean = {
    require(0 <= bits && bits < Integer.SIZE)
    val value1 = value >> (bits - 1)
    value1 == 0 || value1 == -1
  }

  def fitsInNUnsignedBits(bits: Int)(value: Int): Boolean = {
    require(0 <= bits && bits < Integer.SIZE)
    (value >>> bits) == 0
  }

  // Substitutions
  type Subst[T] = Map[T, T]
  def emptySubst[T]: Subst[T] =
    Map.empty[T, T].withDefault(identity)
  def subst[T](from: T, to: T): Subst[T] =
    emptySubst[T] + (from -> to)
  def subst[T](from: Seq[T], to: Seq[T]): Subst[T] =
    emptySubst[T] ++ (from zip to)

  // Fixed point computation
  private def fixedPoint[T](start: T, maxIt: Option[Int])(f: T => T): T = {
    val approx = LazyList.iterate(start, maxIt getOrElse Integer.MAX_VALUE)(f)
    val (improv, stable) = ((approx zip approx.tail) span (p => p._1 != p._2))
    if (improv.isEmpty) stable.head._1 else improv.last._2
  }

  def mapAccumR[A, B, C](start: A, ts: Iterable[B])(f: (A, B) => (A, C)): (A, Iterable[C]) = {
    ts.foldRight((start, Seq[C]())) { case (b, (state, cs)) =>
      val (a, c) = f(state, b)
      (a, c +: cs)
    }
  }

  private[l3] def fixedPoint[T](start: T)(f: T => T): T =
    fixedPoint(start, None)(f)

  private[l3] def fixedPoint[T](start: T, maxIt: Int)(f: T => T): T =
    fixedPoint(start, Some(maxIt))(f)

  type MultiMap[K, V] = Map[K, Set[V]]
  private[l3] case class Graph[Node](
      outEdges: MultiMap[Node, Node],
      inEdges: MultiMap[Node, Node]
  )

  // Strongly connected component algorithm, adapted from:
  // https://eprystupa.wordpress.com/2012/12/29/tarjans-strongly-connected-components-algorithm-in-scala/
  // Based on Tarjans Algorithm:
  // https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
  private[l3] def stronglyConnectedComponents[T](g: Graph[T]): Seq[Set[T]] = {

    type AdjList = MultiMap[T, T]

    def compute(adj: AdjList): Seq[Set[T]] = {

      def strongConnect(state: State, v: T): State = {
        state.visited(v) match {
          case Some(_) => state // Already visited
          case None    =>
            // successors of v
            adj(v)
              .foldLeft(state.visit(v)) { (s, w) =>
                strongConnect(s, w).updateLowLink(v, w)
              }
              .collectScc(v)
        }
      }

      val initialState =
        State(
          visited = Map.empty.withDefault(_ => None),
          next = 0,
          stack = List.empty,
          stacked = Map.empty.withDefault(_ => false),
          results = List.empty
        )

      adj.keys.foldLeft(initialState) { strongConnect(_, _) }.results
    }

    case class Visited(index: Int, lowLink: Int)

    case class State(
        visited: Map[T, Option[Visited]],
        next: Int,
        stack: List[T],
        stacked: Map[T, Boolean],
        results: List[Set[T]]
    ) {
      def collectScc(v: T): State = {
        def pop(r: Set[T], s: List[T]): (Set[T], List[T]) =
          (s: @unchecked) match {
            case w +: ss if w == v => (r + w, ss)
            case w +: ss           => pop(r + w, ss)
          }

        visited(v).get match {
          // If v is a root node, pop the stack and generate an SCC
          case Visited(index, lowLink) if (index == lowLink) =>
            val (scc, remainingStack) = pop(Set.empty, stack)
            val stackedLessScc = scc.foldLeft(stacked) { (s, w) =>
              s + (w -> false)
            }
            copy(
              stack = remainingStack,
              stacked = stackedLessScc,
              results = scc +: results
            )
          case _ => this
        }
      }

      // Mark a vertex visited and increment state
      def visit(v: T) = copy(
        visited = visited + (v -> Some(Visited(next, next))),
        next = next + 1,
        stack = v +: stack,
        stacked = stacked + (v -> true)
      )

      def updateLowLink(v: T, w: T): State =
        (visited(v).get, visited(w).get) match {
          case (vv, ww) if (stacked(w) && ww.lowLink < vv.lowLink) =>
            copy(visited = visited + (v -> Some(Visited(vv.index, ww.lowLink))))
          case _ => this
        }
    }

    compute(g.outEdges.withDefault(_ => Set.empty))
  }
}
