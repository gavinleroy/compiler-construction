package l3

import l3.{ L3Primitive => L3 }
import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree =
    transform(tree) { _ => C.Halt(C.AtomL(IntLit(L3Int(0)))) }

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
            C.Fun(n, k, args, transform(body) { v => C.AppC(k, Seq(v)) })
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
        val c = Symbol.fresh("kont")
        val ct = Symbol.fresh("kont")
        val cf = Symbol.fresh("kont")
        val r = Symbol.fresh("atom")
        transform_seq(args) { c_args =>
          C.LetC(
            Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))),
            C.LetC(
              Seq(
                C.Cnt(ct, Seq(), transform(et) { vt => C.AppC(c, Seq(vt)) })
              ),
              C.LetC(
                Seq(
                  C.Cnt(
                    cf,
                    Seq(),
                    transform(ef) { vf => C.AppC(c, Seq(vf)) }
                  )
                ),
                C.If(p, c_args, ct, cf)
              )
            )
          )
        }
      // If with other expression
      case S.If(cnd, et, ef) =>
        // NOTE by calling fresh before the recursive `transform` calls the IR is easier to read.
        val c = Symbol.fresh("kont")
        val ct = Symbol.fresh("kont")
        val cf = Symbol.fresh("kont")
        val r = Symbol.fresh("atom")
        transform_seq(Seq(cnd)) { c_args =>
          C.LetC(
            Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))),
            C.LetC(
              Seq(
                C.Cnt(ct, Seq(), transform(et) { vt => C.AppC(c, Seq(vt)) })
              ),
              C.LetC(
                Seq(
                  C.Cnt(
                    cf,
                    Seq(),
                    transform(ef) { vf => C.AppC(c, Seq(vf)) }
                  )
                ),
                C.If(
                  L3Primitive.Eq,
                  c_args :+ C.AtomL(BooleanLit(false)),
                  cf,
                  ct
                )
              )
            )
          )
        }
      // Logical primitive application
      case prim @ S.Prim(p: L3TestPrimitive, args) =>
        // NOTE by calling fresh before the recursive `transform` calls the IR is easier to read.
        val c = Symbol.fresh("kont")
        val ct = Symbol.fresh("kont")
        val cf = Symbol.fresh("kont")
        val r = Symbol.fresh("atom")
        transform_seq(args) { c_args =>
          C.LetC(
            Seq(C.Cnt(c, Seq(r), ctx(C.AtomN(r)))),
            C.LetC(
              Seq(
                C.Cnt(ct, Seq(), C.AppC(c, Seq(C.AtomL(BooleanLit(true)))))
              ),
              C.LetC(
                Seq(
                  C.Cnt(
                    cf,
                    Seq(),
                    C.AppC(c, Seq(C.AtomL(BooleanLit(false))))
                  )
                ),
                C.If(p, c_args, ct, cf)
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
    * `(f e1 e2 ...) => (let ((v (f e1 e2 ...))) v)' when the matched expression
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
}
