package l3

import SymbolicCPSTreeModuleLow._

object CPSHoister extends (Tree => LetF) {
  def apply(tree: Tree): LetF =
    tree match {
      case lp @ LetP(name, prim, args, body) => {
        val LetF(funs, bodyp) = apply(body)
        LetF(funs, lp.copy(body = bodyp))
      }

      case LetC(cnts, body) => {
        val (funs, cntsp) = cnts
          .map({ cnt =>
            val LetF(funs, body) = apply(cnt.body)
            (funs, cnt.copy(body = body))
          })
          .unzip
        val LetF(funsp, bodyp) = apply(body)
        LetF(
          funs.flatten ++ funsp,
          LetC(
            cntsp,
            bodyp
          )
        )
      }

      case LetF(funs, body) =>
        val (eFuns, nFuns) = funs
          .map({ fun =>
            val LetF(funsp, bodyp) = apply(fun.body)
            (funsp, fun.copy(body = bodyp))
          })
          .unzip
        val letf = apply(body)
        LetF(nFuns ++ eFuns.flatten ++ letf.funs, letf.body)

      case other =>
        LetF(Seq(), other)
    }
}
