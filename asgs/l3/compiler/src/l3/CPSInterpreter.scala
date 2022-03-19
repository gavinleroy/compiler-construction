package l3

import scala.annotation.tailrec
import scala.collection.mutable.{ Map => MutableMap }
import IO._

/**
  * A tree-based interpreter for the CPS languages.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

sealed abstract class CPSInterpreter[M <: CPSTreeModule](
  protected val treeModule: M,
  log: M#Tree => Unit = { _ : M#Tree => () }) {

  import treeModule._

  def apply(tree: Tree): TerminalPhaseResult =
    Right((eval(tree, emptyEnv), None))

  protected sealed trait Value
  protected case class FunV(retC: Name, args: Seq[Name], body: Tree, env: Env)
      extends Value
  protected case class CntV(args: Seq[Name], body: Tree, env: Env)
      extends Value

  protected type Env = PartialFunction[Name, Value]
  protected val emptyEnv: Env = Map.empty

  @tailrec
  private def eval(tree: Tree, env: Env): Int = {
    def resolve(a: Atom): Value = a match {
      case AtomN(n) => env(n)
      case AtomL(l) => evalLit(l)
    }

    log(tree)

    (tree: @unchecked) match {
      case LetP(name, prim, args, body) =>
        eval(body, Map(name->evalValuePrim(prim, args map resolve)) orElse env)

      case LetC(cnts, body) =>
        val recEnv = MutableMap[Name, Value]()
        val env1 = recEnv orElse env
        for (Cnt(name, args, body) <- cnts)
          recEnv(name) = CntV(args, body, env1)
        eval(body, env1)

      case LetF(funs, body) =>
        val recEnv = MutableMap[Name, Value]()
        val env1 = recEnv orElse env
        for (Fun(name, retC, args, body) <- funs)
          recEnv(name) = wrapFunV(FunV(retC, args, body, env1))
        eval(body, env1)

      case AppC(cnt, args) =>
        val CntV(cArgs, cBody, cEnv) = env(cnt)
        assume(cArgs.length == args.length)
        eval(cBody, (cArgs zip (args map resolve)).toMap orElse cEnv)

      case AppF(fun, retC, args) =>
        val FunV(fRetC, fArgs, fBody, fEnv) = unwrapFunV(resolve(fun))
        assume(fArgs.length == args.length)
        val rArgs = args map resolve
        val env1 = ((fRetC +: fArgs) zip (env(retC) +: rArgs)).toMap orElse fEnv
        eval(fBody, env1)

      case If(cond, args, thenC, elseC) =>
        val cnt = if (evalTestPrim(cond, args map resolve)) thenC else elseC
        val cntV = env(cnt).asInstanceOf[CntV]
        eval(cntV.body, cntV.env)

      case Halt(name) =>
        extractInt(resolve(name))
    }
  }

  protected def extractInt(v: Value): Int

  protected def wrapFunV(funV: FunV): Value
  protected def unwrapFunV(v: Value): FunV

  protected def evalLit(l: Literal): Value
  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value
  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean
}

object CPSInterpreterHigh extends CPSInterpreter(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => TerminalPhaseResult) {
  import treeModule._
  import L3Primitive._

  private case class BlockV(tag: L3BlockTag, contents: Array[Value])
      extends Value
  private case class IntV(value: L3Int) extends Value
  private case class CharV(value: L3Char) extends Value
  private case class BooleanV(value: Boolean) extends Value
  private case object UnitV extends Value

  protected def extractInt(v: Value): Int = v match { case IntV(i) => i.toInt }

  protected def wrapFunV(funV: FunV): Value =
    BlockV(l3.BlockTag.Function.id, Array(funV))
  protected def unwrapFunV(v: Value): FunV = v match {
    case BlockV(id, Array(funV: FunV)) if id == l3.BlockTag.Function.id => funV
  }

  protected def evalLit(l: Literal): Value = l match {
    case IntLit(i) => IntV(i)
    case CharLit(c) => CharV(c)
    case BooleanLit(b) => BooleanV(b)
    case UnitLit => UnitV
  }

  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value =
    (p, args) match {
      case (BlockAlloc(t), Seq(IntV(i))) =>
        BlockV(t, Array.fill(i.toInt)(UnitV))
      case (BlockTag, Seq(BlockV(t, _))) => IntV(L3Int(t))
      case (BlockLength, Seq(BlockV(_, c))) => IntV(L3Int(c.length))
      case (BlockGet, Seq(BlockV(_, v), IntV(i))) => v(i.toInt)
      case (BlockSet, Seq(BlockV(_, v), IntV(i), o)) => v(i.toInt) = o; UnitV

      case (IntAdd, Seq(IntV(v1), IntV(v2))) => IntV(v1 + v2)
      case (IntSub, Seq(IntV(v1), IntV(v2))) => IntV(v1 - v2)
      case (IntMul, Seq(IntV(v1), IntV(v2))) => IntV(v1 * v2)
      case (IntDiv, Seq(IntV(v1), IntV(v2))) => IntV(v1 / v2)
      case (IntMod, Seq(IntV(v1), IntV(v2))) => IntV(v1 % v2)
      case (IntToChar, Seq(IntV(v))) => CharV(v.toInt)

      case (IntShiftLeft, Seq(IntV(v1), IntV(v2))) => IntV(v1 << v2)
      case (IntShiftRight, Seq(IntV(v1), IntV(v2))) => IntV(v1 >> v2)
      case (IntBitwiseAnd, Seq(IntV(v1), IntV(v2))) => IntV(v1 & v2)
      case (IntBitwiseOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 | v2)
      case (IntBitwiseXOr, Seq(IntV(v1), IntV(v2))) => IntV(v1 ^ v2)

      case (ByteRead, Seq()) => IntV(L3Int(readByte()))
      case (ByteWrite, Seq(IntV(c))) => writeByte(c.toInt); UnitV
      case (CharToInt, Seq(CharV(c))) => IntV(L3Int(c))

      case (Id, Seq(v)) => v
    }

  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean =
    (p, args) match {
      case (BlockP, Seq(BlockV(_, _))) => true
      case (BlockP, Seq(_)) => false

      case (IntP, Seq(IntV(_))) => true
      case (IntP, Seq(_)) => false
      case (IntLt, Seq(IntV(v1), IntV(v2))) => v1 < v2
      case (IntLe, Seq(IntV(v1), IntV(v2))) => v1 <= v2

      case (CharP, Seq(CharV(_))) => true
      case (CharP, Seq(_)) => false

      case (BoolP, Seq(BooleanV(_))) => true
      case (BoolP, Seq(_)) => false

      case (UnitP, Seq(UnitV)) => true
      case (UnitP, Seq(_)) => false

      case (Eq, Seq(v1, v2)) => v1 == v2
    }
}

class CPSInterpreterLow(log: SymbolicCPSTreeModuleLow.Tree => Unit)
    extends CPSInterpreter(SymbolicCPSTreeModuleLow, log)
    with (SymbolicCPSTreeModuleLow.Tree => TerminalPhaseResult) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._
  import scala.language.implicitConversions

  protected case class BlockV(addr: Bits32,
                              tag: L3BlockTag,
                              contents: Array[Value])
      extends Value
  protected case class BitsV(value: Bits32) extends Value

  private var nextBlockAddr = 0
  protected def allocBlock(tag: L3BlockTag, contents: Array[Value]): BlockV = {
    val block = BlockV(nextBlockAddr, tag, contents)
    nextBlockAddr += 4
    block
  }

  private implicit def valueToBits(v: Value): Bits32 = v match {
    case BlockV(addr, _, _) => addr
    case BitsV(value)       => value
    case _: FunV | _: CntV  => sys.error(s"cannot convert $v to bits")
  }

  protected def extractInt(v: Value): Int = v match { case BitsV(i) => i }

  protected def wrapFunV(funV: FunV): Value = funV
  protected def unwrapFunV(v: Value): FunV = v.asInstanceOf[FunV]

  protected def evalLit(l: Literal): Value = BitsV(l)

  protected def evalValuePrim(p: ValuePrimitive, args: Seq[Value]): Value =
    (p, args) match {
      case (Add, Seq(v1, v2)) => BitsV(v1 + v2)
      case (Sub, Seq(v1, v2)) => BitsV(v1 - v2)
      case (Mul, Seq(v1, v2)) => BitsV(v1 * v2)
      case (Div, Seq(v1, v2)) => BitsV(v1 / v2)
      case (Mod, Seq(v1, v2)) => BitsV(v1 % v2)

      case (ShiftLeft, Seq(v1, v2)) => BitsV(v1 << v2)
      case (ShiftRight, Seq(v1, v2)) => BitsV(v1 >> v2)
      case (And, Seq(v1, v2)) => BitsV(v1 & v2)
      case (Or, Seq(v1, v2)) => BitsV(v1 | v2)
      case (XOr, Seq(v1, v2)) => BitsV(v1 ^ v2)

      case (ByteRead, Seq()) => BitsV(readByte())
      case (ByteWrite, Seq(c)) => writeByte(c); BitsV(0)

      case (BlockAlloc(t), Seq(BitsV(s))) =>
        allocBlock(t, Array.fill(s)(BitsV(0)))
      case (BlockTag, Seq(BlockV(_, t, _))) => BitsV(t)
      case (BlockLength, Seq(BlockV(_, _, c))) => BitsV(c.length)
      case (BlockGet, Seq(BlockV(_, _, c), BitsV(i))) => c(i)
      case (BlockSet, Seq(BlockV(_, _, c), BitsV(i), v)) =>
        c(i) = v; BitsV(0)

      case (Id, Seq(o)) => o
    }

  protected def evalTestPrim(p: TestPrimitive, args: Seq[Value]): Boolean =
    (p, args) match {
      case (Lt, Seq(v1, v2)) => v1 < v2
      case (Le, Seq(v1, v2)) => v1 <= v2
      case (Eq, Seq(v1, v2)) => v1 == v2
    }
}

object CPSInterpreterLow extends CPSInterpreterLow(_ => ())

object CPSInterpreterLowNoCC extends CPSInterpreterLow(_ => ()) {
  override protected def wrapFunV(funV: FunV): Value =
    allocBlock(BlockTag.Function.id, Array(funV))

  override protected def unwrapFunV(v: Value): FunV = v match {
    case BlockV(_, _, Array(funV: FunV)) => funV
  }
}
