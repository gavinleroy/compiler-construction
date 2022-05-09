package l3

import PCRelativeASMInstructionModule._
import IO._

/**
  * An interpreter for the ASM language.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object ASMInterpreter extends (Seq[Instruction] => TerminalPhaseResult) {
  def apply(program: Seq[Instruction]): TerminalPhaseResult =
    try {
      Right((interpret(program.toArray), None))
    } catch {
      case e: EvalError => Left(e.msg)
    }

  private class EvalError(val msg: String) extends Exception

  private def interpret(program: Array[Instruction]): Int = {
    import scala.language.implicitConversions

    var PC: Bits32 = 0

    def error(msg: String): Nothing =
      throw new EvalError(s"${msg} (at PC = ${PC})")

    implicit def bitsToValue(i: Bits32): Value = BitsV(i)
    implicit def valueToBits(v: Value): Bits32 = v match {
      case BitsV(i) => i
      case BlockV(a, _, _) => a
      case _ => error(s"expected bits, found $v")
    }
    implicit def valueToBlock(v: Value): BlockV = v match {
      case b: BlockV => b
      case _ => error(s"expected block, found $v")
    }

    trait Value
    case class BitsV(value: Bits32) extends Value
    case class BlockV(addr: Bits32, tag: L3BlockTag, contents: Array[Value])
        extends Value
    case object UndefV extends Value

    var nextBlockAddr = 0
    def allocBlock(tag: L3BlockTag, size: Bits32): BlockV = {
      nextBlockAddr += 4
      BlockV(nextBlockAddr, tag, Array.fill(size)(UndefV))
    }

    final class Frame {
      private var savedContext = null : (Int, Frame)
      private var regs = Array.empty[Value]
      private var r223 = (UndefV : Value)

      def apply(i: Int): Value =
        if (i == 223) r223 else regs(i)

      def update(i: Int, v: Value): Unit =
        if (i == 223) r223 = v else regs(i) = v

      def push(vs: Value*): Unit =
        regs = regs.concat(vs)

      def resize(size: Int): Unit =
        if (size < regs.length)
          regs = Array.copyOf(regs, size)
        else if (size > regs.length)
          regs = regs.padTo(size, UndefV)

      def save(context: (Int, Frame)): Unit =
        savedContext = context

      def restore(): (Int, Frame) = {
        val c = savedContext
        savedContext = null
        c
      }
    }

    object R {
      private val constants = Array.tabulate(32)(BitsV(_))

      var currFrame = new Frame()
      var nextFrame = new Frame()

      def apply(r: ASMRegister): Value = r match {
        case ASMRegister.Local(i) => currFrame(i)
        case ASMRegister.Const(i) => constants(i)
        case _ => error(s"invalid register ${r}")
      }

      def update(r: ASMRegister, v: Value): Unit = r match {
        case ASMRegister.Local(i) => currFrame(i) = v
        case _ => error(s"invalid register ${r}")
      }

      def resize(size: Int): Unit =
        currFrame.resize(size)

      def args(aa: Value*): Unit =
        nextFrame.push(aa : _*)

      def pushFrame(savedPc: Int): Unit = {
        nextFrame.save((savedPc, currFrame))
        currFrame = nextFrame
        nextFrame = new Frame()
      }

      def dropFrame(): Unit = {
        nextFrame.save(currFrame.restore())
        currFrame = nextFrame
        nextFrame = new Frame()
      }

      def popFrame(): Int = {
        val (savedPc, savedFrame) = currFrame.restore()
        currFrame = savedFrame
        savedPc
      }
    }

    while (true) {
      program(PC) match {
        case ADD(a, b, c) =>
          R(a) = R(b) + R(c)
          PC += 1

        case SUB(a, b, c) =>
          R(a) = R(b) - R(c)
          PC += 1

        case MUL(a, b, c) =>
          R(a) = R(b) * R(c)
          PC += 1

        case DIV(a, b, c) =>
          R(a) = R(b) / R(c)
          PC += 1

        case MOD(a, b, c) =>
          R(a) = R(b) % R(c)
          PC += 1

        case LSL(a, b, c) =>
          R(a) = R(b) << R(c)
          PC += 1

        case LSR(a, b, c) =>
          R(a) = R(b) >> R(c)
          PC += 1

        case AND(a, b, c) =>
          R(a) = R(b) & R(c)
          PC += 1

        case OR(a, b, c) =>
          R(a) = R(b) | R(c)
          PC += 1

        case XOR(a, b, c) =>
          R(a) = R(b) ^ R(c)
          PC += 1

        case JLT(a, b, d) =>
          PC += (if (R(a) < R(b)) d else 1)

        case JLE(a, b, d) =>
          PC += (if (R(a) <= R(b)) d else 1)

        case JEQ(a, b, d) =>
          PC += (if (R(a) == R(b)) d else 1)

        case JNE(a, b, d) =>
          PC += (if (R(a) != R(b)) d else 1)

        case JI(d) =>
          PC += d

        case CALL_NI(a) =>
          val targetPc = R(a) >> 2
          R.pushFrame(PC + 1)
          PC = targetPc

        case CALL_ND(d) =>
          R.pushFrame(PC + 1)
          PC += d

        case CALL_TI(a) =>
          val targetPc = R(a) >> 2
          R.dropFrame()
          PC = targetPc

        case CALL_TD(d) =>
          R.dropFrame()
          PC += d

        case RET(a) =>
          val retVal = R(a)
          PC = R.popFrame()
          R(ASMRegister.L223) = retVal

        case HALT(a) =>
          return R(a)

        case LDLO(a, s) =>
          R(a) = s
          PC += 1

        case LDHI(a, u) =>
          R(a) = (u << 16) | (R(a) & 0xFFFF)
          PC += 1

        case MOVE(a, b) =>
          R(a) = R(b)
          PC += 1

        case ARGS(a, b, c) =>
          R.args(R(a), R(b), R(c))
          PC += 1

        case FRAME(s) =>
          R.resize(s)
          PC += 1

        case BALO(a, b, t) =>
          R(a) = allocBlock(t, R(b))
          PC += 1

        case BSIZ(a, b) =>
          R(a) = R(b).contents.length
          PC += 1

        case BTAG(a, b) =>
          R(a) = R(b).tag
          PC += 1

        case BGET(a, b, c) =>
          R(a) = R(b).contents(R(c))
          PC += 1

        case BSET(a, b, c) =>
          R(b).contents(R(c)) = R(a)
          PC += 1

        case BREA(a) =>
          R(a) = readByte()
          PC += 1

        case BWRI(a) =>
          writeByte(R(a))
          PC += 1
      }
    }
    0 // should not be needed
  }
}
