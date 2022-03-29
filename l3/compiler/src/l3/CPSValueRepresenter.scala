package l3

import l3.{ CPSTestPrimitive => CPST }
import l3.{ CPSValuePrimitive => CPSV }
import l3.{ L3Primitive => L3 }
import l3.{ SymbolicCPSTreeModule => H }
import l3.{ SymbolicCPSTreeModuleLow => L }

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  private val charTagShift = 3
  private val intTagShift = 1
  private val charTagBits = 0x06
  private val intTagBits = 0x01
  private val falseTagBits = 0x0a
  private val trueTagBits = 0x1a
  private val unitTagBits = 0x02

  // A relation for a given free variable, which associates
  // the block position in the closure and the cooresponding
  // worker and wrapper names.
  private case class FunVariableRelation(
      freeVar: Symbol,
      pos: Int,
      workerName: Symbol = Symbol.fresh("v"),
      wrapperName: Symbol = Symbol.fresh("v")
  )

  // From: Fun name
  // To: (WorkerName, FunVariableRelation for each free variable)
  private type FunRelation = Map[Symbol, (Symbol, Seq[FunVariableRelation])]
  private implicit class FRUtil(m: FunRelation) {
    def fRSUnchecked(s: Symbol): Seq[FunVariableRelation] =
      m.get(s).get._2
  }

  def apply(tree: H.Tree): L.Tree =
    transform(tree)(Map(): FunRelation)

  private def transform(
      tree: H.Tree
  )(implicit knownFuns: FunRelation): L.Tree =
    (tree: @unchecked) match {
      // Cases not involving a primitive
      case H.LetC(cnts, body) =>
        L.LetC(
          cnts map { case H.Cnt(n, args, body) =>
            L.Cnt(n, args, transform(body))
          },
          transform(body)
        )

      // NOTE Closure Conversion
      //
      // Functions are converted into flat closures using the following outline:
      // - A relation is  created for each function, determining free variables
      //   and their associated block position -- functions appearing in the same
      //   `funs' list are mutually visible.
      // - For each function, a worker, wrapper, and series of nested block-set!
      //   expressions are created.
      // - Function declarations are collected and sequenced at the beginning of the
      //   resulting expression. Block declarations are collected and nested before
      //   all inner block-set!s.
      case H.LetF(funs, body) => {

        val freeRelations: FunRelation =
          knownFuns ++ getFreeRelations(knownFuns, funs)

        val (fns, iBody) = funs.foldRight(
          (
            Seq(): Seq[L.Fun],
            transform(body)(freeRelations): L.Tree
          )
        ) {
          case (
                H.Fun(fname, retC, args, fBody),
                (fccs, innerBody)
              ) => {

            // NOTE unsafe get should never fail
            val (wi, rels) = freeRelations.get(fname).get
            val FVSubst: Subst[Symbol] = relationsToSubst(rels)
            val si = Symbol.fresh("s") // wrapper name
            val env1 = Symbol.fresh("env")
            val ki = Symbol.fresh("k")
            val wrapperArgs = args.map(_ => Symbol.fresh("v"))
            val fBodySub =
              substitute(transform(fBody)(freeRelations), FVSubst)

            val worker = L.Fun(
              wi,
              retC,
              args ++ (rels.map(_.workerName)),
              fBodySub
            )

            val wrapper = L.Fun(
              si,
              ki,
              env1 +: wrapperArgs,
              rels.foldRight(
                L.AppF(
                  L.AtomN(wi),
                  ki,
                  wrapperArgs.map(L.AtomN(_))
                    ++ (rels.map(r => L.AtomN(r.wrapperName)))
                ): L.Tree
              ) { (rel, iBody) =>
                L.LetP(
                  rel.wrapperName,
                  CPSV.BlockGet,
                  Seq(L.AtomN(env1), L.AtomL(rel.pos)),
                  iBody
                )
              }
            )

            (
              worker +: wrapper +: fccs,
              templateP(
                CPSV.BlockSet,
                Seq(L.AtomN(fname), L.AtomL(0), L.AtomN(si))
              ) { _ =>
                rels.foldRight(innerBody) { (rel, iBody) =>
                  templateP(
                    CPSV.BlockSet,
                    Seq(L.AtomN(fname), L.AtomL(rel.pos), L.AtomN(rel.freeVar))
                  ) { _ => iBody }
                }
              }
            )
          }
        }
        L.LetF(
          fns,
          funs.foldRight(iBody) { (f, body) =>
            L.LetP(
              f.name,
              CPSV.BlockAlloc(202),
              Seq(L.AtomL(freeRelations.fRSUnchecked(f.name).size + 1)),
              body
            )
          }
        )
      }
      case H.AppF(fun, retc, args) => {
        val fv = rewrite(fun)
        fv match {
          // For known function we can inline application with the worker
          case L.AtomN(fname) if knownFuns contains fname => {
            val (wi, rels) = knownFuns.get(fname).get
            val freeVars = rels map { r => L.AtomN(r.freeVar) }
            L.AppF(
              L.AtomN(wi),
              retc,
              (args map rewrite) ++ freeVars
            )
          }
          case fv =>
            templateP(CPSV.BlockGet, Seq(fv, L.AtomL(0x00))) { fa =>
              L.AppF(fa, retc, fv +: (args map rewrite))
            }
        }
      }
      case H.AppC(cnt, args) =>
        L.AppC(cnt, args map rewrite)

      case H.Halt(a) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(a), L.AtomL(intTagShift))) {
          aa =>
            L.Halt(aa)
        }
      // Cases involving a TestPrimitive
      case H.If(L3.BlockP, Seq(x), tc, fc) =>
        templateP(CPSV.And, Seq(rewrite(x), L.AtomL(0x03))) { xa =>
          L.If(CPST.Eq, Seq(xa, L.AtomL(0x00)), tc, fc)
        }
      case H.If(L3.IntP, Seq(x), tc, fc) =>
        templateP(CPSV.And, Seq(rewrite(x), L.AtomL(0x01))) { xa =>
          L.If(CPST.Eq, Seq(xa, L.AtomL(intTagBits)), tc, fc)
        }
      case H.If(L3.CharP, Seq(x), tc, fc) =>
        templateP(CPSV.And, Seq(rewrite(x), L.AtomL(0x07))) { xa =>
          L.If(CPST.Eq, Seq(xa, L.AtomL(charTagBits)), tc, fc)
        }
      case H.If(L3.BoolP, Seq(x), tc, fc) =>
        templateP(CPSV.And, Seq(rewrite(x), L.AtomL(0x0f))) { xa =>
          // NOTE false / true tag bits are equal for the first 4 LSB,
          // therefore, we can extract only 4 and compare against the false tag bits.
          L.If(CPST.Eq, Seq(xa, L.AtomL(falseTagBits)), tc, fc)
        }
      case H.If(L3.UnitP, Seq(x), tc, fc) =>
        templateP(CPSV.And, Seq(rewrite(x), L.AtomL(0x0f))) { xa =>
          L.If(CPST.Eq, Seq(xa, L.AtomL(unitTagBits)), tc, fc)
        }
      case H.If(L3.IntLt, args, tc, fc) =>
        L.If(CPST.Lt, args map rewrite, tc, fc)
      case H.If(L3.IntLe, args, tc, fc) =>
        L.If(CPST.Le, args map rewrite, tc, fc)
      case H.If(L3.Eq, args, tc, fc) =>
        L.If(CPST.Eq, args map rewrite, tc, fc)
      // -----------------------------
      // Cases involving a ValuePrimitive
      case H.LetP(name, L3.BlockAlloc(tag), Seq(v), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(v), L.AtomL(intTagShift))) {
          va =>
            L.LetP(name, CPSV.BlockAlloc(tag), Seq(va), transform(body))
        }
      case H.LetP(name, L3.BlockTag, Seq(v), body) =>
        templateP(CPSV.BlockTag, Seq(rewrite(v))) { va =>
          templateP(CPSV.ShiftLeft, Seq(va, L.AtomL(intTagShift))) { sva =>
            L.LetP(
              name,
              CPSV.Or,
              Seq(sva, L.AtomL(intTagBits)),
              transform(body)
            )
          }
        }
      case H.LetP(name, L3.BlockLength, Seq(v), body) =>
        templateP(CPSV.BlockLength, Seq(rewrite(v))) { va =>
          templateP(CPSV.ShiftLeft, Seq(va, L.AtomL(intTagShift))) { sva =>
            L.LetP(
              name,
              CPSV.Or,
              Seq(sva, L.AtomL(intTagBits)),
              transform(body)
            )
          }
        }
      case H.LetP(name, L3.BlockGet, Seq(b, n), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(n), L.AtomL(intTagShift))) {
          na =>
            L.LetP(name, CPSV.BlockGet, Seq(rewrite(b), na), transform(body))
        }
      case H.LetP(name, L3.BlockSet, Seq(b, n, v), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(n), L.AtomL(intTagShift))) {
          na =>
            L.LetP(
              name,
              CPSV.BlockSet,
              Seq(rewrite(b), na, rewrite(v)),
              transform(body)
            )
        }
      case H.LetP(name, L3.IntAdd, Seq(a, b), body) =>
        templateP(CPSV.Sub, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          L.LetP(name, CPSV.Add, Seq(aa, rewrite(b)), transform(body))
        }
      case H.LetP(name, L3.IntSub, Seq(a, b), body) =>
        templateP(CPSV.Add, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          L.LetP(name, CPSV.Sub, Seq(aa, rewrite(b)), transform(body))
        }
      case H.LetP(name, L3.IntMul, Seq(a, b), body) =>
        templateP(CPSV.Sub, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          templateP(CPSV.ShiftRight, Seq(rewrite(b), L.AtomL(0x01))) { ba =>
            templateP(CPSV.Mul, Seq(aa, ba)) { va =>
              L.LetP(name, CPSV.Add, Seq(va, L.AtomL(0x01)), transform(body))
            }
          }
        }
      case H.LetP(name, L3.IntDiv, Seq(a, b), body) =>
        templateP(CPSV.Sub, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          templateP(CPSV.Sub, Seq(rewrite(b), L.AtomL(0x01))) { ba =>
            templateP(CPSV.Div, Seq(aa, ba)) { va =>
              templateP(CPSV.ShiftLeft, Seq(va, L.AtomL(intTagShift))) { va =>
                L.LetP(
                  name,
                  CPSV.Or,
                  Seq(va, L.AtomL(intTagBits)),
                  transform(body)
                )
              }
            }
          }
        }
      // NOTE `a % b` cannot be optimized when using tagged integers.
      case H.LetP(name, L3.IntMod, Seq(a, b), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(a), L.AtomL(intTagShift))) {
          aa =>
            templateP(CPSV.ShiftRight, Seq(rewrite(b), L.AtomL(intTagShift))) {
              ba =>
                templateP(CPSV.Mod, Seq(aa, ba)) { va =>
                  templateP(CPSV.ShiftLeft, Seq(va, L.AtomL(intTagShift))) {
                    va =>
                      L.LetP(
                        name,
                        CPSV.Or,
                        Seq(va, L.AtomL(intTagBits)),
                        transform(body)
                      )
                  }
                }
            }
        }
      case H.LetP(name, L3.IntShiftLeft, Seq(a, b), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(b), L.AtomL(intTagShift))) {
          sa =>
            templateP(CPSV.Sub, Seq(rewrite(a), L.AtomL(0x01))) { va =>
              templateP(CPSV.ShiftLeft, Seq(va, sa)) { va =>
                L.LetP(
                  name,
                  CPSV.Or,
                  Seq(va, L.AtomL(intTagBits)),
                  transform(body)
                )
              }
            }
        }
      case H.LetP(name, L3.IntShiftRight, Seq(a, b), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(b), L.AtomL(intTagShift))) {
          sa =>
            templateP(CPSV.ShiftRight, Seq(rewrite(a), sa)) { va =>
              L.LetP(
                name,
                CPSV.Or,
                Seq(va, L.AtomL(intTagBits)),
                transform(body)
              )
            }
        }
      case H.LetP(name, L3.IntBitwiseAnd, args, body) =>
        L.LetP(name, CPSV.And, args map rewrite, transform(body))
      case H.LetP(name, L3.IntBitwiseOr, args, body) =>
        L.LetP(name, CPSV.Or, args map rewrite, transform(body))
      case H.LetP(name, L3.IntBitwiseXOr, Seq(a, b), body) =>
        templateP(CPSV.And, Seq(rewrite(a), L.AtomL(0xfffffffe))) { aa =>
          L.LetP(name, CPSV.XOr, Seq(aa, rewrite(b)), transform(body))
        }
      case H.LetP(name, L3.ByteRead, Seq(), body) =>
        templateP(CPSV.ByteRead, Seq()) { reada =>
          templateP(CPSV.ShiftLeft, Seq(reada, L.AtomL(intTagShift))) { sa =>
            L.LetP(name, CPSV.Or, Seq(sa, L.AtomL(intTagBits)), transform(body))
          }
        }
      case H.LetP(name, L3.ByteWrite, Seq(a), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(a), L.AtomL(intTagShift))) {
          aa =>
            L.LetP(name, CPSV.ByteWrite, Seq(aa), transform(body))
        }
      case H.LetP(name, L3.IntToChar, Seq(a), body) =>
        templateP(CPSV.ShiftLeft, Seq(rewrite(a), L.AtomL(0x02))) { aa =>
          L.LetP(name, CPSV.Or, Seq(aa, L.AtomL(0x02)), transform(body))
        }
      case H.LetP(name, L3.CharToInt, Seq(a), body) =>
        L.LetP(
          name,
          CPSV.ShiftRight,
          Seq(rewrite(a), L.AtomL(0x02)),
          transform(body)
        )
      case H.LetP(name, L3.Id, Seq(arg), body) => {
        val aa = rewrite(arg)
        aa match {
          // NOTE if the argument getting bound 'rhs' is a known
          // function, then the alias 'lhs' should also be a known function.
          // Thus, a copy is created in the set of known relations under
          // the new lhs (name).
          case L.AtomN(fname) if knownFuns contains fname => {
            L.LetP(
              name,
              CPSV.Id,
              Seq(aa),
              transform(body)(knownFuns + (name -> knownFuns.get(fname).get))
            )
          }
          case aa =>
            L.LetP(name, CPSV.Id, Seq(aa), transform(body))
        }
      }
    }

  private def templateP(vPrim: CPSV, args: Seq[L.Atom])(
      innerF: L.Atom => L.Tree
  ): L.Tree = {
    val t = Symbol.fresh("t")
    L.LetP(t, vPrim, args, innerF(L.AtomN(t)))
  }

  /** Rewrite an atom of the high SymbolicCPSTreeModule to use the atom
    * representation of the SymbollicCPSTreeModuleLow. This rewrite uses values
    * as they will be represented in the VM, for example, literal integers are
    * tagged and represented as 32Bit Vectors.
    */
  private def rewrite(a: H.Atom): L.Atom =
    a match {
      case H.AtomN(named) =>
        L.AtomN(named)
      case H.AtomL(IntLit(i)) =>
        L.AtomL((i.toInt << intTagShift) | intTagBits)
      case H.AtomL(BooleanLit(true)) =>
        L.AtomL(trueTagBits)
      case H.AtomL(BooleanLit(false)) =>
        L.AtomL(falseTagBits)
      // NOTE Character is implicitely coerced to code point
      case H.AtomL(CharLit(c)) =>
        L.AtomL((c << charTagShift) | charTagBits)
      case H.AtomL(UnitLit) =>
        L.AtomL(unitTagBits)
    }

  /** Substitution of free variables to fresh symbols.
    *
    * Given a SymbolicTreeModuleLow.Tree and a map (FreeVariable -> Symbol)
    * replace all of the free variables with a fresh symbol.
    */
  private def substitute(tree: L.Tree, s: Subst[Symbol]): L.Tree = {
    def substT(tree: L.Tree): L.Tree =
      tree match {
        case L.LetP(name, prim, args, body) =>
          L.LetP(name, prim, args map substA, substT(body))
        case L.LetC(cnts, body) =>
          L.LetC(cnts map substC, substT(body))
        case L.LetF(funs, body) =>
          L.LetF(funs map substF, substT(body))
        case L.AppC(cnt, args) =>
          L.AppC(cnt, args map substA)
        case L.AppF(fun, retC, args) =>
          L.AppF(substA(fun), retC, args map substA)
        case L.If(cond, args, thenC, elseC) =>
          L.If(cond, args map substA, thenC, elseC)
        case L.Halt(arg) =>
          L.Halt(substA(arg))
      }

    def substC(cnt: L.Cnt): L.Cnt =
      L.Cnt(cnt.name, cnt.args map { n => s.getOrElse(n, n) }, substT(cnt.body))

    def substF(fun: L.Fun): L.Fun =
      L.Fun(
        s.getOrElse(fun.name, fun.name),
        fun.retC,
        fun.args map { n => s.getOrElse(n, n) },
        substT(fun.body)
      )

    def substA(atom: L.Atom): L.Atom =
      atom match {
        case L.AtomN(n) =>
          L.AtomN(s.getOrElse(n, n))
        case a => a
      }

    substT(tree)
  }

  private def relationsToSubst(rs: Seq[FunVariableRelation]): Subst[Symbol] = {
    rs.map({ r => subst(r.freeVar, r.workerName) })
      .foldLeft(emptySubst: Subst[Symbol])({ _ ++ _ })
  }

  /** GetFreeRelations:
    *
    * A free relation relates a function 'f' with it's worker name 'w' in
    * addition to the ordered set of its free variables. `knownFuns' is the
    * currently known functions associated with their relation and `funs' is the
    * sequence of functions for which a relation is desired.
    *
    * getFreeRelations returns a relation for *each member of `funs'* and is
    * _not_ combined with `knownFuns' in any way.
    */
  private def getFreeRelations(
      knownFuns: FunRelation,
      funs: Seq[H.Fun]
  ): FunRelation = {

    /** GetFreeVars
      *
      * Returns a set of free variables for a single function, in the context of
      * the knownFuns. When determining if a symbol is free, a distinction is
      * made between symbols in application position (A) or value position (V).
      *
      * A known function in application position is not considered free, when it
      * is applied this will happen directly through the worker and the closure
      * is not needed -- the free variables of a known function are still
      * considered free for the caller. All symbols in value position are
      * considered free, even those locally bound.
      *
      * All remaining symbols (fun args, LetP lhs, etc ...) are not considered
      * free regardless of position.
      */
    def getFreeVars(fun: H.Fun): Set[Symbol] = {

      object UsePosition extends Enumeration {
        type UsePosition = Value
        val A, V = Value
      }

      import UsePosition._

      val emptySet: Set[(UsePosition, Symbol)] = Set()

      implicit class SeqSetUtil[T](s: Seq[Set[T]]) {
        def unionAll() = s.fold(Set(): Set[T]) { _ | _ }
        def unionAll(b: Set[T]) = s.fold(b) { _ | _ }
      }

      def getFVT(tree: H.Tree): Set[(UsePosition, Symbol)] =
        tree match {
          case H.LetP(name, _, args, body) =>
            args
              .map { getFVA _ }
              .unionAll(getFVT(body) - ((A, name)) - ((V, name)))
          case H.LetC(cnts, body) =>
            cnts
              .map { getFVC _ }
              .unionAll(getFVT(body))
          case H.LetF(funs, body) =>
            funs
              .map { getFVF _ }
              .unionAll(getFVT(body))
              .removedAll((funs.map { f => (A, f.name) }))
              .removedAll((funs.map { f => (V, f.name) }))
          case H.AppC(cnt, args) =>
            args
              .map { getFVA _ }
              .unionAll()
          case H.AppF(fun, retC, args) =>
            args
              .map { getFVA _ }
              .unionAll(
                fun match {
                  case H.AtomN(name) if knownFuns contains name =>
                    // NOTE values in knownFuns are already closed, thus none of them
                    // can be inlined hence the 'V' is used to ensure they remain free.
                    knownFuns
                      .fRSUnchecked(name)
                      .map { t => (V, t.freeVar) }
                      .toSet
                  case H.AtomN(name) =>
                    Set((A, name))
                  case a =>
                    emptySet
                }
              )
          case H.If(cond, args, thenC, elseC) =>
            args
              .map(getFVA _)
              .unionAll()
          case H.Halt(arg) =>
            getFVA(arg)
        }

      def getFVF(fun: H.Fun): Set[(UsePosition, Symbol)] =
        getFVT(fun.body)
          .excl((A, fun.name))
          .removedAll(fun.args map { (A, _) })
          .removedAll(fun.args map { (V, _) })

      def getFVC(cnt: H.Cnt): Set[(UsePosition, Symbol)] =
        getFVT(cnt.body)
          .removedAll(cnt.args map { (A, _) })
          .removedAll(cnt.args map { (V, _) })

      def getFVA(atom: H.Atom): Set[(UsePosition, Symbol)] =
        atom match {
          case H.AtomN(name) =>
            Set((V, name))
          case H.AtomL(_) =>
            emptySet
        }

      getFVF(fun) map { _._2 };
    }

    // NOTE I believe that a single pass is sufficient and the fixpoint
    // is not necessary, however, I did not have sufficient  time to prove
    // this and the fixpoint computation remained for safety.
    def transitiveFreeVars(
        m: Map[Symbol, Set[Symbol]]
    ): Map[Symbol, Set[Symbol]] =
      fixedPoint(m) { mp =>
        mp.foldLeft(mp) { case (nm, (k, v)) =>
          nm + (k -> v.foldLeft(v) { _ | nm.getOrElse(_, v.empty) })
        }
      }

    val freeVars = transitiveFreeVars(
      funs.foldLeft(Map(): Map[Symbol, Set[Symbol]]) { (map, fun) =>
        map + (fun.name -> getFreeVars(fun))
      }
    )

    freeVars.map { case (fname, vs) =>
      (
        fname,
        (
          Symbol.fresh("w"),
          // Give free variables an ordered with block position
          vs.toSeq.zipWithIndex.map { case (fv, pos) =>
            // NOTE increment the position by 1 because position 0
            // is reserved for the code pointer.
            FunVariableRelation(fv, pos + 1)
          }
        )
      )
    }
  }
}
