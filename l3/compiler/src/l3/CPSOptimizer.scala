package l3

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }](
    val treeModule: T
) {
  import treeModule._

  protected def rewrite(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    fixedPoint(simplifiedTree)(shrink)
    // FIXME
    simplifiedTree
    // val maxSize = size(simplifiedTree) * 3 / 2
    // fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  private case class Count(applied: Int = 0, asValue: Int = 0)

  private case class State(
      census: Map[Name, Count],
      aSubst: Subst[Atom] = emptySubst,
      cSubst: Subst[Name] = emptySubst,
      eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
      cEnv: Map[Name, Cnt] = Map.empty,
      fEnv: Map[Name, Fun] = Map.empty
  ) {

    def dead(s: Name): Boolean =
      !census.contains(s)
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1, asValue = 0))

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
  }

  // Shrinking optimizations

  // ------------ TODO ------------
  // [-] dead code elimination (DCE),
  // [-] common subexpression elimination (CSE),
  // [-] constant propogation,
  // [-] constant folding,
  // [-] simplifications due to neutral/absorbing elements,
  // [-] shrinking inlining,
  //
  // TODO for later
  // [ ] general inlining, using the heuristic described below,
  // [ ] additional optimizations if you wish, e.g. those related to blocks.
  // ------------------------------

  private def shrink(tree: Tree): Tree =
    shrink(tree, State(census(tree)))

  private def shrink(tree: Tree, s: State): Tree = tree match {
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
        // IFF the prim/args pair was already seen, remove let and subst names
        case (p, args) if s.eInvEnv contains (p, args) =>
          shrink(body, s.withASubst(name, s.eInvEnv((p, args))))
        case (p, args) if !impure(p) && !unstable(p) =>
          LetP(
            name,
            prim,
            args,
            // TODO associative operations, e.g. IntAdd
            shrink(body, s.withExp(name, p, args))
          )
        case (p, args) =>
          LetP(name, prim, args, shrink(body, s))
      }
    }

    case LetC(cnts, body) => {
      val (toInline: Seq[Cnt], oths: Seq[Cnt]) =
        cnts.partition { k => s.appliedOnce(k.name) }
      val shrunkCnts = oths.foldRight(cnts.empty) {
        case (Cnt(name, args, body), ks) =>
          if (s.dead(name))
            ks
          else Cnt(name, args, shrink(body, s)) +: ks
      }
      LetC(shrunkCnts, shrink(body, s.withCnts(toInline)))
    }

    case LetF(funs, body) => {
      val censi = funs map { f => census(f.body) }
      val (toInline: Seq[Fun], oths: Seq[Fun]) =
        // NOTE a function can get inlined (shrinking) if
        // it is (1) applied once and (2) isn't free in any
        // of the mutually recursive functions.
        funs.partition { f =>
          s.appliedOnce(f.name) && !censi.exists { _.contains(f.name) }
        }
      val shrunkFuns = oths.foldRight(funs.empty) {
        case (Fun(name, retC, args, body), fs) =>
          if (s.dead(name))
            fs
          else Fun(name, retC, args, shrink(body, s)) +: fs
      }
      LetF(shrunkFuns, shrink(body, s.withFuns(toInline)))
    }

    case AppC(cntPrev, argsPrev) =>
      (s.aSubst(AtomN(cntPrev)), argsPrev map s.aSubst) match {
        case (AtomN(cnt), args: Seq[Atom]) if s.cEnv contains cnt =>
          val k = s.cEnv(cnt)
          shrink(k.body, s.withASubst(k.args, args))
        case (AtomN(cnt), args) =>
          AppC(cnt, args)
      }

    case AppF(fun, retCPrev, argsPrev) =>
      val AtomN(retC) = s.aSubst(AtomN(retCPrev))
      (s.aSubst(fun), argsPrev map s.aSubst) match {
        case (AtomN(f), args: Seq[Atom]) if s.fEnv contains f =>
          val fun = s.fEnv(f)
          shrink(
            fun.body,
            s.withASubst(fun.retC +: fun.args, AtomN(retC) +: args)
          )
        case (f, args) =>
          AppF(f, retC, args)
      }

    case If(condPrim, argsPrev, thenC, elseC) =>
      val args = argsPrev map s.aSubst
      args match {
        case Seq(AtomL(x), AtomL(y))
            if cEvaluator.isDefinedAt((condPrim, Seq(x, y))) =>
          if (cEvaluator((condPrim, Seq(x, y))))
            AppC(thenC, Seq())
          else AppC(elseC, Seq())
        case Seq(x, y) if x == y =>
          if (sameArgReduceC(condPrim))
            AppC(thenC, Seq())
          else AppC(elseC, Seq())
        case _ =>
          If(condPrim, args, thenC, elseC)
      }

    case Halt(arg) =>
      Halt(s.aSubst(arg))

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

    val trees = LazyList.iterate((0, tree), fibonacci.length) {
      case (i, tree) =>
        val funLimit = fibonacci(i)
        val cntLimit = i

        def sameLen[T, U](formalArgs: Seq[T], actualArgs: Seq[U]): Boolean =
          formalArgs.length == actualArgs.length

        def inlineT(tree: Tree)(implicit s: State): Tree = ???

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

    case (Eq, Seq(IntLit(x), IntLit(y)))         => x == y
    case (Eq, Seq(CharLit(x), CharLit(y)))       => x == y
    case (Eq, Seq(BooleanLit(x), BooleanLit(y))) => x == y
    case (Eq, Seq(UnitLit, UnitLit))             => true
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
