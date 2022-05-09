package l3

/**
  * A module for ASM instructions.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

trait ASMInstructionModule {
  type Label
  type Constant

  sealed abstract class Instruction

  case class ADD(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class SUB(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class MUL(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class DIV(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class MOD(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction

  case class LSL(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class LSR(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class AND(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class OR(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class XOR(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction

  case class JLT(a: ASMRegister, b: ASMRegister, d: Constant)
      extends Instruction
  case class JLE(a: ASMRegister, b: ASMRegister, d: Constant)
      extends Instruction
  case class JEQ(a: ASMRegister, b: ASMRegister, d: Constant)
      extends Instruction
  case class JNE(a: ASMRegister, b: ASMRegister, d: Constant)
      extends Instruction
  case class JI(d: Label) extends Instruction

  case class CALL_NI(r: ASMRegister) extends Instruction
  case class CALL_ND(d: Label) extends Instruction
  case class CALL_TI(r: ASMRegister) extends Instruction
  case class CALL_TD(d: Label) extends Instruction
  case class RET(r: ASMRegister) extends Instruction
  case class HALT(r: ASMRegister) extends Instruction

  case class LDLO(a: ASMRegister, s: Constant) extends Instruction
  case class LDHI(a: ASMRegister, u: Int) extends Instruction
  case class MOVE(a: ASMRegister, b: ASMRegister) extends Instruction
  case class ARGS(a: ASMRegister, b: ASMRegister, c: ASMRegister)
      extends Instruction
  case class FRAME(s: Int) extends Instruction

  case class BALO(a: ASMRegister, b: ASMRegister, t: L3BlockTag)
      extends Instruction
  case class BSIZ(a: ASMRegister, b: ASMRegister) extends Instruction
  case class BTAG(a: ASMRegister, b: ASMRegister) extends Instruction
  case class BGET(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction
  case class BSET(a: ASMRegister, b: ASMRegister, c: ASMRegister)
       extends Instruction

  case class BREA(a: ASMRegister) extends Instruction
  case class BWRI(a: ASMRegister) extends Instruction

  sealed case class LabeledInstruction(labels: Set[Label],
                                       instruction: Instruction) {
    override def toString: String =
      labels.map(l => s"$l:\n").mkString + "        " + instruction
  }

  def nl(i: Instruction): LabeledInstruction =
    LabeledInstruction(Set.empty, i)
  def labeled(labels: Set[Label], code: LabeledProgram): LabeledProgram =
    code match {
      case Seq(LabeledInstruction(labels1, i1), rest @ _*) =>
        LabeledInstruction(labels1 ++ labels, i1) +: rest
    }
  def labeled(label: Label, code: LabeledProgram): LabeledProgram =
    labeled(Set(label), code)

  type Program = Seq[Instruction]
  type LabeledProgram = Seq[LabeledInstruction]
}

/**
  * A module for ASM instructions labeled explicitly by a symbol.
  */
object LabeledASMInstructionModule extends ASMInstructionModule {
  type Label = Symbol
  sealed trait Constant {
    override def toString: String = this match {
      case LabelC(l) => l.toString
      case IntC(v) => v.toString
    }
  }
  case class LabelC(l: Label) extends Constant
  case class IntC(v: Int) extends Constant
}

/**
  * A module for ASM instructions labeled implicitly by their
  * position.
  */
object PCRelativeASMInstructionModule extends ASMInstructionModule {
  type Label = Int
  type Constant = Int
}
