package l3

import l3.{ L3Primitive => L3 }
import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree =
    transform(tree) { _ => C.Halt(C.AtomL(IntLit(L3Int(0)))) }

  /** Transforms a SymbolicCL3Tree to a SymbolicCPSTree assuming that the `tree`
    * is *not* in tail position. Specific optimization cases are found later in
    * the file, see below.
    */
  private def transform(tree: S.Tree)(implicit ctx: C.Atom => C.Tree): C.Tree =
    tree match {
      // Trivial cases
      case S.Ident(n) => ctx(C.AtomN(n))
      case S.Lit(l)   => ctx(C.AtomL(l))
      // Let cases
      case S.Let(bndgs, body) =>
        bndgs.foldRight(transform(body)) { case ((n, e), acc) =>
          transform(e) { v =>
            C.LetP(n, L3Primitive.Id, Seq(v), acc)
          }
        }
      // Letrec cases
      case S.LetRec(fs, body) =>
        C.LetF(
          fs map { case S.Fun(n, args, body) =>
            val k = Symbol.fresh("kont")
            C.Fun(
              n,
              k,
              args,
              transform_tailrec(body, k) // XXX tail position
              // transform(body) { v => C.AppC(k, Seq(v)) }
            )
          },
          transform(body)
        )
      // Application
      case S.App(f, args) =>
        transform_seq(args) { c_args =>
          transform(f) { vf =>
            val c = Symbol.fresh("kont")
            val r = Symbol.fresh("kont")
            C.LetC(
              Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))),
              C.AppF(vf, c, c_args)
            )
          }
        }
      // If with logical primitive
      case S.If(S.Prim(p: L3TestPrimitive, args), et, ef) =>
        // NOTE by calling fresh before the recursive `transform` calls the IR is easier to read.
        val k = Symbol.fresh("kont")
        val kt = Symbol.fresh("kont")
        val kf = Symbol.fresh("kont")
        val r = Symbol.fresh("atom")
        transform_seq(args) { c_args =>
          C.LetC(
            Seq(C.Cnt(k, Seq(r), ctx(C.AtomN(r)))),
            C.LetC(
              Seq(
                // XXX tail call
                C.Cnt(
                  kt,
                  Seq(),
                  transform_tailrec(et, k)
                  // transform(et) { vt => C.AppC(c, Seq(vt)) }
                )
              ),
              C.LetC(
                Seq(
                  C.Cnt(
                    kf,
                    Seq(),
                    transform_tailrec(ef, k) // XXX tail call
                    // transform(ef) { vf => C.AppC(c, Seq(vf)) }
                  )
                ),
                C.If(p, c_args, kt, kf)
              )
            )
          )
        }
      // If with other expression
      case S.If(cnd, et, ef) =>
        // NOTE by calling fresh before the recursive `transform` calls the IR is easier to read.
        val k = Symbol.fresh("kont")
        val kt = Symbol.fresh("kont")
        val kf = Symbol.fresh("kont")
        val r = Symbol.fresh("atom")
        C.LetC(
          Seq(C.Cnt(k, Seq(r), ctx(C.AtomN(r)))),
          C.LetC(
            Seq(
              C.Cnt(
                kt,
                Seq(),
                transform_tailrec(et, k) // XXX tail rec
                // transform(et) { vt => C.AppC(c, Seq(vt)) }
              )
            ),
            C.LetC(
              Seq(
                C.Cnt(
                  kf,
                  Seq(),
                  transform_tailrec(ef, k) // XXX tail rec
                  // transform(ef) { vf => C.AppC(c, Seq(vf)) }
                )
              ),
              transform_cond(cnd, kt, kf) // XXX possible nested if ctx
            )
          )
        )

      // Logical primitive application
      case S.Prim(p: L3TestPrimitive, args) =>
        // NOTE by calling fresh before the recursive `transform` calls the IR is easier to read.
        val k = Symbol.fresh("kont")
        val kt = Symbol.fresh("kont")
        val kf = Symbol.fresh("kont")
        val r = Symbol.fresh("atom")
        transform_seq(args) { c_args =>
          C.LetC(
            Seq(C.Cnt(k, Seq(r), ctx(C.AtomN(r)))),
            C.LetC(
              Seq(
                C.Cnt(kt, Seq(), C.AppC(k, Seq(C.AtomL(BooleanLit(true)))))
              ),
              C.LetC(
                Seq(
                  C.Cnt(
                    kf,
                    Seq(),
                    C.AppC(k, Seq(C.AtomL(BooleanLit(false))))
                  )
                ),
                C.If(p, c_args, kt, kf)
              )
            )
          )
        }
      // Other primitive application
      case S.Prim(p: L3ValuePrimitive, args) =>
        transform_seq(args) { c_args =>
          val n = Symbol.fresh("prim")
          C.LetP(n, p, c_args, ctx(C.AtomN(n)))
        }
      // Halt with expression
      case S.Halt(arg) =>
        transform(arg) { C.Halt(_) }
    }

  /** Transform a sequence of arguments collecting the result before passing
    * into a continuation. This is usefull when doing transformation of the form
    * `(f e1 e2 ...) => (let ((v (f e1 e2 ...))) v)` when the matched expression
    * template is internally represented as a Seq[E].
    */
  private def transform_seq(from: Seq[S.Tree], to: Seq[C.Atom] = Seq())(implicit
      ctx: Seq[C.Atom] => C.Tree
  ): C.Tree =
    from match {
      case Seq() =>
        ctx(to)
      case hd +: tl =>
        transform(hd) { v_i =>
          transform_seq(tl, to :+ v_i)
        }
    }

  /** Transform a SymbolicCL3Tree `tree` and immediatly give the result to the
    * continuation `k`. This is used when the context of a transformation would
    * simply apply the result to a continuation and this will bypass an
    * unnecessary binding.
    */
  private def transform_tailrec(tree: S.Tree, k: Symbol): C.Tree =
    // TODO FIXME make this actually apply continuation directly
    transform(tree) { v => C.AppC(k, Seq(v)) }

  /** Transform a SymbolicCL3Tree `tree` **that appeared in the conditional of
    * an if node**. This case can then be specialized to jump to the direct
    * continuation when one of the branches has a literal value in it.
    *
    * NOTE: if `tree` is not itself an S.If node then transformation occurs as
    * usual.
    */
  private def transform_cond(tree: S.Tree, kt: Symbol, kf: Symbol): C.Tree =
    tree match {
      // IF AST when both branches are BooleanLit
      case S.If(cnd, S.Lit(BooleanLit(b1)), S.Lit(BooleanLit(b2))) =>
        transform_cond(cnd, if (b1) kt else kf, if (b2) kt else kf)
      // IF AST when both left branche is a BooleanLit
      case S.If(cnd, S.Lit(BooleanLit(b1)), ef) =>
        val kkf = Symbol.fresh("kont")
        C.LetC(
          Seq(C.Cnt(kkf, Seq(), transform_cond(ef, kt, kf))),
          transform_cond(cnd, if (b1) kt else kf, kkf)
        )
      // IF AST when both right branche is a BooleanLit
      case S.If(cnd, et, S.Lit(BooleanLit(b1))) =>
        val kkt = Symbol.fresh("kont")
        C.LetC(
          Seq(C.Cnt(kkt, Seq(), transform_cond(et, kt, kf))),
          transform_cond(cnd, kkt, if (b1) kt else kf)
        )
      // Not an S.If node so we transform as before
      case tree =>
        transform(tree) { cnd_arg =>
          C.If(
            L3Primitive.Eq,
            Seq(cnd_arg, C.AtomL(BooleanLit(false))),
            kf,
            kt
          )
        }
    }
}
