package l3

import scala.collection.mutable.{ Map => MutableMap }

/* NOTE to GRADER
 *
 * In addition to the optimizations in this file, I also implemented
 * a contification pass which lives in the 'CPSContifier'. This pass
 * also does things like constant propagation and DCE to make
 * contification more effective.
 * */

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }](
    val treeModule: T
) {
  import treeModule._

  protected def rewrite(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  private case class Count(applied: Int = 0, asValue: Int = 0)
  private case class BlockUsage(
      inApp: Int = 0,
      inSet: Int = 0,
      inGet: Int = 0
  ) {
    def +(that: BlockUsage): BlockUsage =
      copy(
        inApp = inApp + that.inApp,
        inSet = inSet + that.inSet,
        inGet = inGet + that.inGet
      )
  }

  def sameLen[T, U](formalArgs: Seq[T], actualArgs: Seq[U]): Boolean =
    formalArgs.length == actualArgs.length

  private case class State(
      census: Map[Name, Count],
      blockUsage: Map[Name, BlockUsage] = Map.empty,
      aSubst: Subst[Atom] = emptySubst,
      cSubst: Subst[Name] = emptySubst,
      // Expression Env
      eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
      // Continuation Env
      cEnv: Map[Name, Cnt] = Map.empty,
      // Function Env
      fEnv: Map[Name, Fun] = Map.empty,
      // Block Env
      bEnv: Set[Name] = Set.empty
  ) {

    def dead(s: Name): Boolean =
      !census.contains(s)
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1, asValue = 0))

    def canRemoveBlock(b: Name): Boolean = {
      blockUsage.get(b) match {
        // NOTE this case should never happen
        case None => true
        case Some(bu) =>
          bu.inApp == 0 &&
            bu.inGet == 0
      }
    }

    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Name, to: Atom): State =
      withASubst(AtomN(from), to)
    def withASubst(from: Name, to: Literal): State =
      withASubst(from, AtomL(to))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from.map(AtomN) zip to.map(aSubst)))

    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Atom]): State =
      withExp(AtomN(name), prim, args)

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))

    def withBlock(b: Name): State =
      copy(bEnv = bEnv + b)
    def namedBlock(b: Name): Boolean =
      (blockUsage contains b)

    def havocBlock(b: Name): State =
      copy(eInvEnv = eInvEnv.filterNot {
        case ((prim, Seq(AtomN(bname), _)), _) if prim == blockGet =>
          b == bname
        case _ => false
      })
    def havocBlocks(bs: Iterable[Name]): State =
      bs.foldLeft(this) { _.havocBlock(_) }
    /* NOTE havocing all blocks removes the opportunity for some optimizations.
     * E.G.
     * ```scheme
     * (@byte-write 65)
     * (def iters 100000)
     *
     * ;; ref2 should be unboxed and inlined
     * (def ref2 (box iters))
     *
     * (def inc! ;; int box -> unit
     *      (fun (b)
     *           (box-set! b (@+ (unbox b) 1))))
     *
     * (def ref (box 0))
     *
     * (rec loop ((i iters))
     *      (if (not (@= i 0))
     *          (begin (inc! ref)
     *                 (loop (@- i 1)))))
     *
     * (if (@= (unbox ref)
     *         (unbox ref2))
     *     (@byte-write 66)
     *     (@byte-write 63))
     * ```
     * The box `ref2` could ideally be unboxed and the
     * integer value inlined directly. However, by calling havocBlocks()
     * at function/continuation boundaries, this will never happen. I
     * ran out of time trying to implement a [correct] version that
     * properly unboxes `ref2` without ruining the operations on `ref`.
     */
    def havocBlocks(): State =
      copy(eInvEnv = eInvEnv.filterNot {
        case ((prim, Seq(AtomN(bname), _)), _) if prim == blockGet =>
          true
        case _ => false
      })
  }

  // Shrinking optimizations

  /** Shrink Exception
    *
    * There are times when an assumption failed during the shrinking process.
    * The motivating example is function inlining. If a function can be inlined,
    * its definition is removed from the `LetF` node and inlined later, however,
    * if the single application of this function is called with the wrong arity,
    * the inlining should *not* happen. If it did, the resulting error to the
    * user is usually 'variable ??? is undefined'. However, this error is
    * useless because in the source code it definitely is defined. By preserving
    * the function, the proper error message will be displayed.
    *
    * The solution using CPS style is perhaps a little 'overkill' for this very
    * specific use case but I prefer it to throwing an exception etc. My hope is
    * it will make handling other [currently unforseen] issues easy.
    */
  sealed trait ShrinkException
  case class BadApp(fname: Name) extends ShrinkException

  private def shrink(tree: Tree): Tree = {

    val c = census(tree)
    val b = blockUsage(tree)
    shrink(tree, State(c, b))(
      x => x,
      _ => throw new Exception("[bug] shrinking inline critical failure")
    )
  }

  private def shrink(tree: Tree, s: State)(implicit
      continue: Tree => Tree,
      fail: ShrinkException => Tree
  ): Tree = (tree: @unchecked) match {
    case LetP(name, prim, argsPrev, body) => {
      (prim, argsPrev map s.aSubst) match {
        // IFF name is dead and function isn't impure
        case (p, _) if (!impure(p) && s.dead(name)) =>
          shrink(body, s)
        // IFF the primitive is Id propogate atom
        case (p, Seq(a)) if (p == identity) =>
          shrink(body, s.withASubst(name, a))
        // IFF all args are literal we can constant fold (value)
        case (p, Seq(AtomL(x), AtomL(y)))
            if vEvaluator.isDefinedAt((p, Seq(x, y))) =>
          val value: Literal = vEvaluator((p, Seq(x, y)))
          shrink(body, s.withASubst(name, value))
        // IFF neutral/absorbing argument
        case (p, Seq(AtomL(x), y)) if leftNeutral contains (x, p) =>
          shrink(body, s.withASubst(name, y))
        case (p, Seq(AtomL(x), y)) if leftAbsorbing contains (x, p) =>
          shrink(body, s.withASubst(name, AtomL(x)))
        case (p, Seq(x, AtomL(y))) if rightNeutral contains (p, y) =>
          shrink(body, s.withASubst(name, x))
        case (p, Seq(x, AtomL(y))) if rightAbsorbing contains (p, y) =>
          shrink(body, s.withASubst(name, AtomL(y)))
        case (p, Seq(x, y)) if x == y && sameArgReduce.isDefinedAt((p, x)) =>
          val value = sameArgReduce((p, x))
          shrink(body, s.withASubst(name, value))
        case (p, args @ Seq(AtomN(bname), _))
            if p == blockGet &&
              (s.eInvEnv contains (p, args)) =>
          shrink(
            body,
            s.withASubst(name, s.eInvEnv((p, args)))
          )

        // IFF the prim/args pair was already seen, remove let and subst names
        case (p, args) if s.eInvEnv contains (p, args) =>
          shrink(
            body,
            s.withASubst(name, s.eInvEnv((p, args)))
          )
        case (p, args) if !impure(p) && !unstable(p) =>
          shrink(body, s.withExp(name, p, args))(
            b => continue(LetP(name, prim, args, b)),
            fail
          )
        // If the block was identified as removable, get rid of the set.
        case (p, Seq(AtomN(bname), _, _)) if p == blockSet && s.bEnv(bname) =>
          shrink(body, s)
        // TODO remove Subsequent BlocSet to the same slot before a get
        //
        // The next use of BlockGet can have the value inlined
        case (p, args @ Seq(b @ AtomN(bname), n, v)) if p == blockSet =>
          val ns = s.withExp(v, blockGet, Seq(b, n))
          shrink(body, ns)(b => continue(LetP(name, p, args, b)), fail)
        case (blockAlloc, args @ Seq(sizeA))
            if blockAllocTag.isDefinedAt(blockAlloc) =>
          // Remove unused blocks
          if (s.canRemoveBlock(name))
            shrink(body, s.withBlock(name))
          else {
            // IFF allocating a block, you can inline all retrievals of
            // (1) it's size (2) it's tag
            val ns = s
              .withExp(sizeA, blockLength, Seq(AtomN(name)))
              .withExp(
                AtomL(blockAllocTag(blockAlloc)),
                blockTag,
                Seq(AtomN(name))
              )
            shrink(body, ns)(b => continue(LetP(name, prim, args, b)), fail)
          }
        case (p, args) =>
          shrink(body, s)(b => continue(LetP(name, prim, args, b)), fail)
      }
    }
    // Remove empty Let expressions
    case LetC(Seq(), body) => shrink(body, s)
    case LetF(Seq(), body) => shrink(body, s)
    case LetC(cnts, body) =>
      val ns = s.havocBlocks()

      def shrink_seq(from: Seq[Cnt], to: Seq[Cnt] = Seq())(implicit
          cont: Seq[Cnt] => Tree
      ): Tree = from match {
        case Seq() =>
          cont(to)
        case Cnt(name, args, body) +: tl =>
          if (ns.dead(name))
            shrink_seq(tl, to)
          else
            shrink(body, ns)(
              b => shrink_seq(tl, to :+ Cnt(name, args, b)),
              fail
            )
      }
      shrink_seq(cnts) { shrunkCnts =>
        val censi = shrunkCnts map { k => census(k.body) }
        val (toInline: Seq[Cnt], oths: Seq[Cnt]) =
          shrunkCnts.partition { k =>
            ns.appliedOnce(k.name) && !censi.exists { _.contains(k.name) }
          }
        shrink(body, ns.withCnts(toInline))(
          b => continue(LetC(oths, b)),
          fail
        )
      }
    case LetF(funs, body) =>
      val ns = s.havocBlocks()

      def shrink_seq(from: Seq[Fun], to: Seq[Fun] = Seq())(implicit
          cont: Seq[Fun] => Tree
      ): Tree = from match {
        case Seq() =>
          cont(to)
        case Fun(name, retC, args, body) +: tl =>
          if (ns.dead(name))
            shrink_seq(tl, to)
          else
            shrink(body, ns)(
              b => shrink_seq(tl, to :+ Fun(name, retC, args, b)),
              fail
            )
      }
      shrink_seq(funs) { shrunkFuns =>
        val censi = shrunkFuns map { f => census(f.body) }
        val (toInline: Seq[Fun], oths: Seq[Fun]) =
          // NOTE a function can get inlined (shrinking) if
          // it is (1) applied once and (2) isn't free in any
          // of the mutually recursive functions.
          shrunkFuns.partition { f =>
            ns.appliedOnce(f.name) && !censi.exists { _.contains(f.name) }
          }
        // If any inline attemp fails, remove it's name from the
        // inline list and shrink the tree again.
        def failK(mInline: Map[Name, Fun], mFuns: Map[Name, Fun])(
            e: ShrinkException
        ): Tree = e match {
          case BadApp(fname) if mInline contains fname =>
            val fun = mInline(fname)
            val newInlines = mInline - fname
            val newFuns = mFuns + (fname -> fun)
            shrink(body, ns.withFuns(newInlines.values.toSeq))(
              b => continue(LetF(newFuns.values.toSeq, b)),
              failK(newInlines, newFuns)
            )
          case exc =>
            fail(exc)
        }

        val mInline: Map[Name, Fun] =
          (toInline map { f => (f.name, f) }).toMap
        val mFuns: Map[Name, Fun] = (oths map { f => (f.name, f) }).toMap

        shrink(body, ns.withFuns(mInline.values.toSeq))(
          { b =>
            continue(
              if (mFuns.isEmpty)
                b
              else LetF(mFuns.values.toSeq, b)
            )
          },
          failK(mInline, mFuns)
        )
      }
    case AppC(cntPrev, argsPrev) =>
      (s.cSubst(cntPrev), argsPrev map s.aSubst) match {
        case (cnt, args: Seq[Atom]) if s.cEnv contains cnt =>
          val k = s.cEnv(cnt)
          shrink(k.body, s.withASubst(k.args, args))
        case (cnt, args) =>
          continue(AppC(cnt, args))
      }
    case AppF(fun, retCPrev, argsPrev) =>
      val retC = s.cSubst(retCPrev)
      (s.aSubst(fun), argsPrev map s.aSubst) match {
        case (AtomN(f), args: Seq[Atom]) if (s.fEnv contains f) =>
          val fun = s.fEnv(f)
          if (sameLen(fun.args, args))
            shrink(
              fun.body,
              s.withASubst(fun.args, args).withCSubst(fun.retC, retC)
            )
          // do not inline on an application with incorrect arity
          else fail(BadApp(f))
        case (f, args) =>
          continue(AppF(f, retC, args))
      }
    case If(condPrim, argsPrev, thenCP, elseCP) =>
      val args = argsPrev map s.aSubst
      val thenC = s.cSubst(thenCP)
      val elseC = s.cSubst(elseCP)
      args match {
        case Seq(AtomL(x)) if cEvaluator.isDefinedAt((condPrim, Seq(x))) =>
          if (cEvaluator((condPrim, Seq(x))))
            continue(AppC(thenC, Seq()))
          else continue(AppC(elseC, Seq()))
        case Seq(AtomL(x), AtomL(y))
            if cEvaluator.isDefinedAt((condPrim, Seq(x, y))) =>
          if (cEvaluator((condPrim, Seq(x, y))))
            continue(AppC(thenC, Seq()))
          else continue(AppC(elseC, Seq()))
        case Seq(x, y) if x == y =>
          if (sameArgReduceC(condPrim))
            continue(AppC(thenC, Seq()))
          else continue(AppC(elseC, Seq()))
        case args =>
          continue(If(condPrim, args, thenC, elseC))
      }
    case Halt(arg) =>
      continue(Halt(s.aSubst(arg)))
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(tree: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = {
      (tree: @unchecked) match {
        case LetP(name, prim, args, body) =>
          val name1 = name.copy()
          LetP(
            name1,
            prim,
            args map subV,
            copyT(body, subV + (AtomN(name) -> AtomN(name1)), subC)
          )
        case LetC(cnts, body) =>
          val names = cnts map (_.name)
          val names1 = names map (_.copy())
          val subC1 = subC ++ (names zip names1)
          LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
        case LetF(funs, body) =>
          val names = funs map (_.name)
          val names1 = names map (_.copy())
          val subV1 = subV ++ ((names map AtomN) zip (names1 map AtomN))
          LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
        case AppC(cnt, args) =>
          AppC(subC(cnt), args map subV)
        case AppF(fun, retC, args) =>
          AppF(subV(fun), subC(retC), args map subV)
        case If(cond, args, thenC, elseC) =>
          If(cond, args map subV, subC(thenC), subC(elseC))
        case Halt(arg) =>
          Halt(subV(arg))
      }
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy())
      val subV1 = subV ++ ((cnt.args map AtomN) zip (args1 map AtomN))
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy()
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy())
      val subV1 = subV ++ ((fun.args map AtomN) zip (args1 map AtomN))
      val AtomN(funName1) = subV(AtomN(fun.name))
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)
    val loopUnroll = Seq(1, 2, 4, 5, 6, 7)

    /* NOTE if a continuation has a recursive call in tail
     * position, inlining the call is equivalent to loop
     * unrolling.
     *
     * Here, I've decided to allow continuations and functions
     * to be inlined even if they are recursive, but only up to a
     * certain point. With some testing, I've found that allowing
     * functions to inline *slightly* at a higher rate than continuations
     * provides pretty good performance without too huge of resulting trees.
     * */

    val trees = LazyList.iterate((0, tree), fibonacci.length) {
      case (i, tree) =>
        val funLimit = fibonacci(i)
        val loopLimit = loopUnroll(i)
        val cntLimit = i

        def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
          case LetP(name, prim, args, body) =>
            LetP(name, prim, args map s.aSubst, inlineT(body))
          case LetC(cnts, body) =>
            val zipped: Seq[(Cnt, Option[Cnt])] = cnts map {
              case Cnt(name, args, body) =>
                val newK = Cnt(name, args, inlineT(body))
                val mySize = size(body)
                val dont = (mySize > cntLimit) ||
                  (mySize > loopLimit && census(body).contains(name))
                (newK, if (dont) None else Some(newK))
            }
            val (iKs, toInline) = zipped.unzip
            LetC(iKs, inlineT(body)(s.withCnts(toInline.flatten)))
          case LetF(funs, body) =>
            val zipped: Seq[(Fun, Option[Fun])] = funs map {
              case (Fun(name, retC, args, body)) =>
                val newF = Fun(name, retC, args, inlineT(body))
                val mySize = size(body)
                val dont = (mySize > funLimit) ||
                  (mySize > loopLimit && census(body).contains(name))
                (newF, if (dont) None else Some(newF))
            }
            val (iFs, toInline) = zipped.unzip
            LetF(iFs, inlineT(body)(s.withFuns(toInline.flatten)))
          // IFF a continuation or function exists in the state,
          // copy the body and inline
          case AppC(cnt, args) =>
            (s.cSubst(cnt), args map s.aSubst) match {
              case (k, args) if s.cEnv contains cnt =>
                val cnt = s.cEnv(k)
                copyT(
                  cnt.body,
                  subst(cnt.args map { AtomN }, args),
                  emptySubst
                )
              case (cnt, args) =>
                AppC(cnt, args)
            }

          case AppF(fun, retCP, args) =>
            val retC = s.cSubst(retCP)
            (s.aSubst(fun), args map s.aSubst) match {
              case (AtomN(f), args) if (s.fEnv contains f) =>
                val fun = s.fEnv(f)
                if (sameLen(fun.args, args))
                  copyT(
                    fun.body,
                    subst(fun.args map { AtomN }, args),
                    subst(fun.retC, retC)
                  )
                else
                  AppF(AtomN(f), retC, args)
              case (fun, args) =>
                AppF(fun, retC, args)
            }
          case If(cond, args, thenCP, elseCP) =>
            val thenC = s.cSubst(thenCP)
            val elseC = s.cSubst(elseCP)
            If(cond, args map s.aSubst, thenC, elseC)
          case Halt(arg) =>
            Halt(s.aSubst(arg))
        }

        (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile { case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(applied = currCount.applied + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incAppUseA(atom: Atom): Unit =
      atom.asName.foreach(incAppUseN(_))

    def incValUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(asValue = currCount.asValue + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incValUseA(atom: Atom): Unit =
      atom.asName.foreach(incValUseN(_))

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetP(_, _, args, body) =>
        args foreach incValUseA; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUseN(cnt); args foreach incValUseA
      case AppF(fun, retC, args) =>
        incAppUseA(fun); incValUseN(retC); args foreach incValUseA
      case If(_, args, thenC, elseC) =>
        args foreach incValUseA; incValUseN(thenC); incValUseN(elseC)
      case Halt(arg) =>
        incValUseA(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  // FIXME this could be coupled with the cesnsus computation to
  // reduce the number of tree traversals.
  private def blockUsage(tree: Tree): Map[Name, BlockUsage] = {
    val blocks = MutableMap[Name, BlockUsage]().withDefault(_ => BlockUsage())
    val rhs = MutableMap[Name, Tree]()
    def useSet(atom: Atom): Unit =
      atom.asName.foreach { b =>
        val curr = blocks(b)
        blocks(b) = curr.copy(inSet = curr.inSet + 1)
      }
    def useGet(atom: Atom): Unit =
      atom.asName.foreach { b =>
        val curr = blocks(b)
        blocks(b) = curr.copy(inGet = curr.inGet + 1)
      }
    def useApp(atom: Atom): Unit =
      atom.asName.foreach { b =>
        val curr = blocks(b)
        blocks(b) = curr.copy(inApp = curr.inApp + 1)
        rhs.remove(b).foreach(blockUsage)
      }
    def blockUsage(tree: Tree): Unit = (tree: @unchecked) match {
      case LetP(b, p, args, body) if blockAllocTag.isDefinedAt(p) =>
        args foreach useApp; blockUsage(body)
      case LetP(_, p, b +: args, body) if p == blockSet =>
        useSet(b); args foreach useApp; blockUsage(body)
      case LetP(_, p, b +: args, body) if p == blockGet =>
        useGet(b); args foreach useApp; blockUsage(body)
      case LetP(_, _, args, body) =>
        args foreach useApp; blockUsage(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); blockUsage(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); blockUsage(body)
      case AppC(cnt, args) =>
        args foreach useApp
        rhs.remove(cnt).foreach(blockUsage)
      case AppF(fun, retC, args) =>
        args foreach useApp
        fun.asName.foreach { b => rhs.remove(b).foreach(blockUsage) }
        rhs.remove(retC).foreach(blockUsage)
      case If(_, args, thenC, elseC) =>
        args foreach useApp
        rhs.remove(thenC).foreach(blockUsage)
        rhs.remove(elseC).foreach(blockUsage)
      case Halt(arg) =>
        useApp(arg)
    }

    blockUsage(tree)
    blocks.toMap
  }

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body)      => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body)      => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive
  protected val blockSet: ValuePrimitive
  protected val blockGet: ValuePrimitive

  protected val identity: ValuePrimitive
  protected val truthy: Literal
  protected val falsey: Literal

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[
    (ValuePrimitive, Seq[Literal]),
    Literal
  ]
  protected val cEvaluator: PartialFunction[
    (TestPrimitive, Seq[Literal]),
    Boolean
  ]
}

object CPSOptimizerHigh
    extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._
  import L3Primitive._

  def apply(tree: Tree): Tree =
    rewrite(tree)

  import scala.language.implicitConversions
  private[this] implicit def l3IntToLit(i: L3Int): Literal = IntLit(i)
  private[this] implicit def intToLit(i: Int): Literal = IntLit(L3Int(i))

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _                                   => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength
  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id
  protected val truthy: Literal = BooleanLit(true)
  protected val falsey: Literal = BooleanLit(false)

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set(
      (0, IntAdd),
      (1, IntMul),
      (~0, IntBitwiseAnd),
      (0, IntBitwiseOr),
      (0, IntBitwiseXOr)
    )
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set(
      (IntAdd, 0),
      (IntSub, 0),
      (IntMul, 1),
      (IntDiv, 1),
      (IntShiftLeft, 0),
      (IntShiftRight, 0),
      (IntBitwiseAnd, ~0),
      (IntBitwiseOr, 0),
      (IntBitwiseXOr, 0)
    )

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set(
      (0, IntMul),
      (0, IntDiv),
      (0, IntShiftLeft),
      (0, IntShiftRight),
      (0, IntBitwiseAnd),
      (~0, IntBitwiseOr)
    )
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((IntMul, 0), (IntBitwiseAnd, 0), (IntBitwiseOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (IntBitwiseAnd | IntBitwiseOr, a)    => a
    case (IntSub | IntMod | IntBitwiseXOr, _) => AtomL(0)
    case (IntDiv, _)                          => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case IntLe | Eq => true
    case IntLt      => false
  }

  protected val vEvaluator
      : PartialFunction[(ValuePrimitive, Seq[Literal]), Literal] = {
    case (IntAdd, Seq(IntLit(x), IntLit(y)))                 => x + y
    case (IntSub, Seq(IntLit(x), IntLit(y)))                 => x - y
    case (IntMul, Seq(IntLit(x), IntLit(y)))                 => x * y
    case (IntDiv, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x / y
    case (IntMod, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x % y
    case (CharToInt, Seq(CharLit(c)))                        => L3Int(c)
    case (IntToChar, Seq(IntLit(i))) if Character.isValidCodePoint(i.toInt) =>
      CharLit(i.toInt)
    case (IntShiftLeft, Seq(IntLit(x), IntLit(y)))  => x << y
    case (IntShiftRight, Seq(IntLit(x), IntLit(y))) => x >> y
    case (IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => x & y
    case (IntBitwiseOr, Seq(IntLit(x), IntLit(y)))  => x | y
    case (IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => x ^ y
  }

  protected val cEvaluator
      : PartialFunction[(TestPrimitive, Seq[Literal]), Boolean] = {
    case (IntP, Seq(IntLit(_)))      => true
    case (CharP, Seq(CharLit(_)))    => true
    case (BoolP, Seq(BooleanLit(_))) => true
    case (UnitP, Seq(UnitLit))       => true

    case (IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (IntLe, Seq(IntLit(x), IntLit(y))) => x <= y

    // NOTE Eq works for all literals only if they are equivalent.
    case (Eq, Seq(x, y)) => x == y
  }
}

object CPSOptimizerLow
    extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.LetF => SymbolicCPSTreeModuleLow.LetF) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._

  def apply(tree: LetF): LetF = rewrite(tree) match {
    case tree @ LetF(_, _) => tree
    case other             => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _                                   => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength
  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id
  protected val truthy: Literal = 0x1a
  protected val falsey: Literal = 0x0a

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, Add), (1, Mul), (~0, And), (0, Or), (0, XOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set(
      (Add, 0),
      (Sub, 0),
      (Mul, 1),
      (Div, 1),
      (ShiftLeft, 0),
      (ShiftRight, 0),
      (And, ~0),
      (Or, 0),
      (XOr, 0)
    )

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, Mul), (0, Div), (0, ShiftLeft), (0, ShiftRight), (0, And), (~0, Or))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((Mul, 0), (And, 0), (Or, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (And | Or, a)        => a
    case (Sub | Mod | XOr, _) => AtomL(0)
    case (Div, _)             => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Le | Eq => true
    case Lt      => false
  }

  protected val vEvaluator
      : PartialFunction[(ValuePrimitive, Seq[Literal]), Literal] = {
    case (Add, Seq(x, y))                 => x + y
    case (Sub, Seq(x, y))                 => x - y
    case (Mul, Seq(x, y))                 => x * y
    case (Div, Seq(x, y)) if y.toInt != 0 => x / y
    case (Mod, Seq(x, y)) if y.toInt != 0 => x % y

    case (ShiftLeft, Seq(x, y))  => x << y
    case (ShiftRight, Seq(x, y)) => x >> y
    case (And, Seq(x, y))        => x & y
    case (Or, Seq(x, y))         => x | y
    case (XOr, Seq(x, y))        => x ^ y
  }

  protected val cEvaluator
      : PartialFunction[(TestPrimitive, Seq[Literal]), Boolean] = {
    case (Lt, Seq(x, y)) => x < y
    case (Le, Seq(x, y)) => x <= y
    case (Eq, Seq(x, y)) => x == y
  }
}
