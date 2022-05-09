package l3

import l3.{ LabeledASMInstructionModule => L }
import l3.{ PCRelativeASMInstructionModule => R }

/**
  * Label resolution for the ASM language. Translates a program in
  * which addresses are represented as symbolic labels to one where
  * they are represented as PC-relative (or absolute, in some cases)
  * addresses.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object ASMLabelResolver extends (L.LabeledProgram => R.Program) {
  def apply(labeledProgram: L.LabeledProgram): R.Program =
    resolve(fixedPoint(labeledProgram)(expand))

  private def expand(program: L.LabeledProgram): L.LabeledProgram = {
    val indexedProgram = program.zipWithIndex
    val labelAddr = labelMap(indexedProgram)

    (for ((labeledInstr, addr) <- indexedProgram) yield {
       def delta(l: L.Label): Int = labelAddr(l) - addr
       val expanded = labeledInstr.instruction match {
         case L.JLT(a, b, L.LabelC(l)) if !fitsInNSignedBits(11)(delta(l)) =>
           Seq(L.nl(L.JLE(b, a, L.IntC(2))), L.nl(L.JI(l)))
         case L.JLE(a, b, L.LabelC(l)) if !fitsInNSignedBits(11)(delta(l)) =>
           Seq(L.nl(L.JLT(b, a, L.IntC(2))), L.nl(L.JI(l)))
         case L.JEQ(a, b, L.LabelC(l)) if !fitsInNSignedBits(11)(delta(l)) =>
           Seq(L.nl(L.JNE(a, b, L.IntC(2))), L.nl(L.JI(l)))
         case L.JNE(a, b, L.LabelC(l)) if !fitsInNSignedBits(11)(delta(l)) =>
           Seq(L.nl(L.JEQ(a, b, L.IntC(2))), L.nl(L.JI(l)))
         // TODO: LDLO
         case _ => Seq(labeledInstr)
       }
       L.labeled(labeledInstr.labels, expanded)
     }).flatten
  }

  private def resolve(program: L.LabeledProgram): R.Program = {
    val indexedProgram = program.zipWithIndex
    val labelAddr = labelMap(indexedProgram)

    for ((labeledInstr, addr) <- indexedProgram) yield {
      def delta(l: L.Label): Int = labelAddr(l) - addr
      labeledInstr.instruction match {
        case L.ADD(a, b, c)           => R.ADD(a, b, c)
        case L.SUB(a, b, c)           => R.SUB(a, b, c)
        case L.MUL(a, b, c)           => R.MUL(a, b, c)
        case L.DIV(a, b, c)           => R.DIV(a, b, c)
        case L.MOD(a, b, c)           => R.MOD(a, b, c)
        case L.LSL(a, b, c)           => R.LSL(a, b, c)
        case L.LSR(a, b, c)           => R.LSR(a, b, c)
        case L.AND(a, b, c)           => R.AND(a, b, c)
        case L.OR(a, b, c)            => R.OR(a, b, c)
        case L.XOR(a, b, c)           => R.XOR(a, b, c)
        case L.JLT(a, b, L.IntC(d))   => R.JLT(a, b, d)
        case L.JLT(a, b, L.LabelC(l)) => R.JLT(a, b, delta(l))
        case L.JLE(a, b, L.IntC(d))   => R.JLE(a, b, d)
        case L.JLE(a, b, L.LabelC(l)) => R.JLE(a, b, delta(l))
        case L.JEQ(a, b, L.IntC(d))   => R.JEQ(a, b, d)
        case L.JEQ(a, b, L.LabelC(l)) => R.JEQ(a, b, delta(l))
        case L.JNE(a, b, L.IntC(d))   => R.JNE(a, b, d)
        case L.JNE(a, b, L.LabelC(l)) => R.JNE(a, b, delta(l))
        case L.JI(l)                  => R.JI(delta(l))
        case L.CALL_NI(a)             => R.CALL_NI(a)
        case L.CALL_ND(l)             => R.CALL_ND(delta(l))
        case L.CALL_TI(a)             => R.CALL_TI(a)
        case L.CALL_TD(l)             => R.CALL_TD(delta(l))
        case L.RET(a)                 => R.RET(a)
        case L.HALT(a)                => R.HALT(a)
        case L.LDLO(a, L.IntC(s))     => R.LDLO(a, s)
        case L.LDLO(a, L.LabelC(l))   => R.LDLO(a, labelAddr(l) << 2)
        case L.LDHI(a, u)             => R.LDHI(a, u)
        case L.MOVE(a, b)             => R.MOVE(a, b)
        case L.ARGS(a, b, c)          => R.ARGS(a, b, c)
        case L.FRAME(s)               => R.FRAME(s)
        case L.BALO(a, b, t)          => R.BALO(a, b, t)
        case L.BSIZ(a, b)             => R.BSIZ(a, b)
        case L.BTAG(a, b)             => R.BTAG(a, b)
        case L.BGET(a, b, c)          => R.BGET(a, b, c)
        case L.BSET(a, b, c)          => R.BSET(a, b, c)
        case L.BREA(a)                => R.BREA(a)
        case L.BWRI(a)                => R.BWRI(a)
      }
    }
  }

  private def labelMap(program: Seq[(L.LabeledInstruction, Int)])
      : Map[L.Label, Int] =
    (for ((L.LabeledInstruction(labels, _), a) <- program; l <- labels)
     yield (l, a)).toMap
}
