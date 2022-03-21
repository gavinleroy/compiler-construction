package l3

import l3.{ CPSTestPrimitive => CPST }
import l3.{ CPSValuePrimitive => CPSV }
import l3.{ L3Primitive => L3 }
import l3.{ SymbolicCPSTreeModule => H }
import l3.{ SymbolicCPSTreeModuleLow => L }

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  // Constant values used throughout
  // NOTE It was mentioned in the assignment description
  // to use bitsToIntMSBF but I prefer to use hexadecimal numbers.
  private val charTagShift = 3
  private val intTagShift = 1
  private val charTagBits = 0x06
  private val intTagBits = 0x01
  private val falseTagBits = 0x0a
  private val trueTagBits = 0x1a
  private val unitTagBits = 0x02

  def apply(tree: H.Tree): L.Tree =
    (tree: @unchecked) match {
      // Cases not involving a primitive
      case H.LetC(cnts, body) =>
        L.LetC(
          cnts map { case H.Cnt(n, args, body) => L.Cnt(n, args, apply(body)) },
          apply(body)
        )
      case H.LetF(funs, body) =>
        L.LetF(
          funs map { case H.Fun(n, retc, args, body) =>
            L.Fun(n, retc, args, apply(body))
          },
          apply(body)
        )
      case H.AppC(cnt, args) =>
        L.AppC(cnt, args map rewrite)
      case H.AppF(fun, retc, args) =>
        L.AppF(rewrite(fun), retc, args map rewrite)
      case H.Halt(a) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(a), L.AtomL(intTagShift))) {
          aa => L.Halt(aa)
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
            L.LetP(name, CPSV.BlockAlloc(tag), Seq(va), apply(body))
        }
      case H.LetP(name, L3.BlockTag, Seq(v), body) =>
        templateP(CPSV.BlockTag, Seq(rewrite(v))) { va =>
          templateP(CPSV.ShiftLeft, Seq(va, L.AtomL(intTagShift))) { sva =>
            L.LetP(name, CPSV.Or, Seq(sva, L.AtomL(intTagBits)), apply(body))
          }
        }
      case H.LetP(name, L3.BlockLength, Seq(v), body) =>
        templateP(CPSV.BlockLength, Seq(rewrite(v))) { va =>
          templateP(CPSV.ShiftLeft, Seq(va, L.AtomL(intTagShift))) { sva =>
            L.LetP(name, CPSV.Or, Seq(sva, L.AtomL(intTagBits)), apply(body))
          }
        }
      case H.LetP(name, L3.BlockGet, Seq(b, n), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(n), L.AtomL(intTagShift))) {
          na =>
            L.LetP(name, CPSV.BlockGet, Seq(rewrite(b), na), apply(body))
        }
      case H.LetP(name, L3.BlockSet, Seq(b, n, v), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(n), L.AtomL(intTagShift))) {
          na =>
            L.LetP(
              name,
              CPSV.BlockSet,
              Seq(rewrite(b), na, rewrite(v)),
              apply(body)
            )
        }
      case H.LetP(name, L3.IntAdd, Seq(a, b), body) =>
        templateP(CPSV.Sub, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          L.LetP(name, CPSV.Add, Seq(aa, rewrite(b)), apply(body))
        }
      case H.LetP(name, L3.IntSub, Seq(a, b), body) =>
        templateP(CPSV.Add, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          L.LetP(name, CPSV.Sub, Seq(aa, rewrite(b)), apply(body))
        }
      case H.LetP(name, L3.IntMul, Seq(a, b), body) =>
        templateP(CPSV.Sub, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          templateP(CPSV.ShiftRight, Seq(rewrite(b), L.AtomL(0x01))) { ba =>
            templateP(CPSV.Mul, Seq(aa, ba)) { va =>
              L.LetP(name, CPSV.Add, Seq(va, L.AtomL(0x01)), apply(body))
            }
          }
        }
      case H.LetP(name, L3.IntDiv, Seq(a, b), body) =>
        templateP(CPSV.Sub, Seq(rewrite(a), L.AtomL(0x01))) { aa =>
          templateP(CPSV.Sub, Seq(rewrite(b), L.AtomL(0x01))) { ba =>
            templateP(CPSV.Div, Seq(aa, ba)) { va =>
              templateP(CPSV.ShiftLeft, Seq(va, L.AtomL(intTagShift))) { va =>
                L.LetP(name, CPSV.Or, Seq(va, L.AtomL(intTagBits)), apply(body))
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
                        apply(body)
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
                L.LetP(name, CPSV.Or, Seq(va, L.AtomL(intTagBits)), apply(body))
              }
            }
        }
      case H.LetP(name, L3.IntShiftRight, Seq(a, b), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(b), L.AtomL(intTagShift))) {
          sa =>
            templateP(CPSV.ShiftRight, Seq(rewrite(a), sa)) { va =>
              L.LetP(name, CPSV.Or, Seq(va, L.AtomL(intTagBits)), apply(body))
            }
        }
      case H.LetP(name, L3.IntBitwiseAnd, args, body) =>
        L.LetP(name, CPSV.And, args map rewrite, apply(body))
      case H.LetP(name, L3.IntBitwiseOr, args, body) =>
        L.LetP(name, CPSV.Or, args map rewrite, apply(body))
      case H.LetP(name, L3.IntBitwiseXOr, Seq(a, b), body) =>
        templateP(CPSV.And, Seq(rewrite(a), L.AtomL(0xfffffffe))) { aa =>
          L.LetP(name, CPSV.XOr, Seq(aa, rewrite(b)), apply(body))
        }
      case H.LetP(name, L3.ByteRead, Seq(), body) =>
        templateP(CPSV.ByteRead, Seq()) { reada =>
          templateP(CPSV.ShiftLeft, Seq(reada, L.AtomL(intTagShift))) { sa =>
            L.LetP(name, CPSV.Or, Seq(sa, L.AtomL(intTagBits)), apply(body))
          }
        }
      case H.LetP(name, L3.ByteWrite, Seq(a), body) =>
        templateP(CPSV.ShiftRight, Seq(rewrite(a), L.AtomL(intTagShift))) {
          aa =>
            L.LetP(name, CPSV.ByteWrite, Seq(aa), apply(body))
        }
      case H.LetP(name, L3.IntToChar, Seq(a), body) =>
        templateP(CPSV.ShiftLeft, Seq(rewrite(a), L.AtomL(0x02))) { aa =>
          L.LetP(name, CPSV.Or, Seq(aa, L.AtomL(0x02)), apply(body))
        }
      case H.LetP(name, L3.CharToInt, Seq(a), body) =>
        L.LetP(
          name,
          CPSV.ShiftRight,
          Seq(rewrite(a), L.AtomL(0x02)),
          apply(body)
        )
      case H.LetP(name, L3.Id, args, body) =>
        L.LetP(name, CPSV.Id, args map rewrite, apply(body))

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
}
