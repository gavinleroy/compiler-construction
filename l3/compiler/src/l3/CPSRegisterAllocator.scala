package l3

import l3.{ SymbolicCPSTreeModuleLow => S }
import l3.{ RegisterCPSTreeModule => R }
import l3.{ CPSValuePrimitive => CPS }

/**
  * A simple register allocator for CPS/L₃.
  *
  * Parallel-move algorithm taken from "Tilting at windmills with Coq"
  * by Rideau et al.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object CPSRegisterAllocator extends (S.LetF => R.LetF) {
  def apply(prog: S.LetF): R.LetF = {
    val rLink = R.Reg(ASMRegister.Link)
    R.LetF(prog.funs map { case S.Fun(name, retC, args, body) =>
             val rArgs = ASMRegister.locals.take(args.length).map(R.Reg)
             val s = initialState(body)
               .withAssignedReg(retC, rLink)
               .withAssignedRegs(args, rArgs)
             R.Fun(R.Label(name), rLink, rArgs, rewrite(body, s))
           },
           rewrite(prog.body, initialState(prog.body)))
  }

  private val L223 = R.Reg(ASMRegister.L223)

  private def rewrite(tree: S.Tree, s: State): R.Tree = tree match {
    case S.LetP(name, CPS.Id, Seq(S.AtomL(l)), body) =>
      s.withFreshRegFor(name, body) { (r, s) =>
        R.LetP(r, CPS.Id, Seq(R.AtomL(l)), rewrite(body, s))
      }

    case S.LetP(name, prim, args, body) =>
      s.withFreshRegFor(name, body) { (r, s) =>
        s.withRegsContaining(args, tree) { (rArgs, s) =>
          R.LetP(r, prim, rArgs map R.AtomN, rewrite(body, s))
        }
      }

    case S.LetC(cnts, body) =>
      s.withContinuations(cnts) { s =>
        val s1 = cnts.foldLeft(s) { (s, c) =>
          if (s.retConts(c.name)) {
            assume(c.args.length == 1)
            s.withCntArgs(c.name, Seq(L223))
          } else {
            s.withFreshRegsFor(c.args, c.body) { (rs, s) =>
              s.withCntArgs(c.name, rs)
            }
          }
        }
        R.LetC(cnts map (rewrite(_, s1)), rewrite(body, s1))
      }

    case S.AppC(cont, args) =>
      s.withRegsContaining(args, tree) { (rArgs, s) =>
        val rOutC = s.cArgs.getOrElse(cont, rArgs)
        s.withParallelCopy(rOutC, rArgs, tree)(
          R.AppC(s.rOrL(cont), rOutC map R.AtomN))
      }

    case S.AppF(S.AtomN(fun), retC, args) =>
      s.withRegsContaining(args, tree) { (rArgs, s) =>
        R.AppF(R.AtomN(s.rOrL(fun)), s.rOrL(retC), rArgs map R.AtomN)
      }

    case S.If(cond, args, thenC, elseC) =>
      s.withRegsContaining(args, tree) { (rArgs, _) =>
        R.If(cond, rArgs map R.AtomN, R.Label(thenC), R.Label(elseC)) }

    case S.Halt(arg) =>
      s.withRegContaining(arg, tree) { (rArg, _) =>
        R.Halt(R.AtomN(rArg)) }
  }

  private def rewrite(cnt: S.Cnt, s: State): R.Cnt = {
    if (s.retConts(cnt.name))
      s.withFreshRegFor(cnt.args.head, cnt.body) { (r, s) =>
        R.Cnt(R.Label(cnt.name),
              Seq(L223),
              R.LetP(r, CPS.Id, Seq(R.AtomN(L223)), rewrite(cnt.body, s))) }
    else
      R.Cnt(R.Label(cnt.name), s.cArgs(cnt.name), rewrite(cnt.body, s))
  }

  private case class State(retConts: Set[S.Name],
                           cLiveVars: Map[S.Name, Set[S.Name]] = Map.empty,
                           regs: Map[S.Name, R.Reg] = Map.empty,
                           cArgs: Map[S.Name, Seq[R.Reg]] = Map.empty) {
    def withAssignedReg(name: S.Name, reg: R.Reg) =
      copy(regs = regs + (name -> reg))
    def withAssignedRegs(names: Seq[S.Name], regs: Seq[R.Reg]) = {
      require(names.length == regs.length)
      copy(regs = this.regs ++ (names zip regs))
    }

    def withCntArgs(name: S.Name, args: Seq[R.Reg]) =
      copy(cArgs = cArgs + (name -> args))

    def withContinuations[T](cnts: Seq[S.Cnt])
                         (body: State => T): T = {
      val emptyCLiveVars = Map(cnts map { c => c.name -> Set[S.Name]() } : _*)
      val cLiveVars1 = fixedPoint(emptyCLiveVars) { cLiveVarsApprox =>
        val s1 = copy(cLiveVars = cLiveVars ++ cLiveVarsApprox)
        Map(cnts map { c => c.name -> s1.liveVariables(c.body) } : _*)
      }
      body(copy(cLiveVars = cLiveVars ++ cLiveVars1))
    }

    def withFreshRegFor[T](name: S.Name, cont: S.Tree)
                       (body: (R.Reg, State) => T): T =
      withFreshRegsFor(Seq(name), cont) { case (Seq(r), s) => body(r, s) }

    def withFreshRegsFor[T](names: Seq[S.Name], cont: S.Tree)
                        (body: (Seq[R.Reg], State) => T): T = {
      val live = liveVariables(cont) flatMap ((regs andThen (_.reg)).lift(_))
      val free = ASMRegister.locals
        .filterNot(live)
        .take(names.length)
        .map(R.Reg)
      assert(free.length == names.length,
             s"not enough local registers (${names.length} requested)")
      body(free, withAssignedRegs(names, free))
    }

    def withRegContaining(atom: S.Atom, cont: S.Tree)
                         (body: (R.Reg, State) => R.Tree): R.Tree = atom match {
      case S.AtomN(name) =>
        (regs get name map (body(_, this))) getOrElse {
          withFreshRegFor(name, cont) { (r, s) =>
            R.LetP(r, CPS.Id, Seq(R.AtomN(R.Label(name))), body(r, s)) }
        }
      case S.AtomL(l) =>
        body(R.Reg(ASMRegister.consts(l)), this)
    }

    def withRegsContaining(atoms: Seq[S.Atom], cont: S.Tree)
                          (body: (Seq[R.Reg], State) => R.Tree): R.Tree =
      atoms match {
        case Seq() =>
          body(Seq(), this)
        case Seq(n, ns @ _*) =>
          withRegContaining(n, cont) { (rN, s) =>
            withRegsContaining(ns, cont) { (rNs, s) => body(rN +: rNs, s) } }
      }

    def withParallelCopy(toS: Seq[R.Reg], fromS: Seq[R.Reg], cont: S.Tree)
                        (body: R.Tree): R.Tree = {
      type Move = (R.Reg, R.Reg)

      def splitMove(t: Seq[Move], d: R.Reg)
          : Option[(Seq[Move], R.Reg, Seq[Move])] =
        (t span (_._1 != d)) match {
          case (_, Seq())            => None
          case (pre, (_, r) +: post) => Some(pre, r, post)
        }

      def loop(toMove: Seq[Move], beingMoved: Seq[Move], moved: Seq[Move])
          : Seq[Move] = {
        (toMove, beingMoved, moved) match {
          case (Seq(), Seq(), m) =>
            m.reverse
          case ((s, d) +: tl, b @ Seq(), m) if s == d =>
            loop(tl, b, m)
          case (t +: ts, Seq(), m) =>
            loop(ts, Seq(t), m)
          case (t, (sd @ (s, d)) +: b, m) =>
            splitMove(t, d) match {
              case Some((t1, r, t2)) =>
                loop(t1 ++ t2, (d, r) +: sd +: b, m)
              case None =>
                b match {
                  case Seq() =>
                    loop(t, Seq(), sd +: m)
                  case _ if b.last._1 == d =>
                    val temp = Symbol.fresh("parMoveTmp")
                    withFreshRegFor(temp, cont) { (tmp, _) =>
                      loop(t, b.init :+ ((tmp, b.last._2)), sd +: (d, tmp) +: m)
                    }
                  case _ =>
                    loop(t, b, sd +: m)
                }
            }
        }
      }
      val moves = loop(fromS zip toS, Seq.empty, Seq.empty)
      moves.foldRight(body) { case ((s, d), b) =>
          R.LetP(d, CPS.Id, Seq(R.AtomN(s)), b)
      }
    }

    def rOrL(name: S.Name): R.Name =
      regs.getOrElse(name, R.Label(name))

    def liveVariables(tree: S.Tree): Set[S.Name] = tree match {
      case S.LetP(_, _, args, body) =>
        liveVariables(body) ++ args.flatMap(_.asName)
      case S.LetC(cnts, body) =>
        val s1 = copy(cLiveVars =
                        cLiveVars ++ (cnts map { c => c.name -> Set[S.Name]()}))
        s1.liveVariables(body) ++ (
          cnts flatMap { c => s1.liveVariables(c.body) })
      case S.AppC(cont, args) =>
        cLiveVars.getOrElse(cont, Set()) ++ args.flatMap(_.asName)
      case S.AppF(fun, retC, args) =>
        (cLiveVars.getOrElse(retC, Set()) ++ (fun +: args).flatMap(_.asName))
      case S.If(_, args, thenC, elseC) =>
        cLiveVars(thenC) ++ cLiveVars(elseC) ++ args.flatMap(_.asName)
      case S.Halt(arg) =>
        arg.asName.toSet
    }
  }

  private def initialState(tree: S.Tree): State = {
    def retContsT(tree: S.Tree): Set[S.Name] = tree match {
      case S.LetP(_, _, _, body) => retContsT(body)
      case S.LetC(cnts, body) => retContsT(body) ++ (cnts flatMap retContsC)
      case S.AppF(_, retC, _) => Set(retC)
      case S.AppC(_, _) | S.If(_, _, _, _) | S.Halt(_) => Set.empty
    }

    def retContsC(cnt: S.Cnt): Set[S.Name] =
      retContsT(cnt.body)

    State(retConts = retContsT(tree))
  }
}
