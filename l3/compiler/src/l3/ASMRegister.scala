package l3

sealed abstract class ASMRegister(val name: String) {
  override def toString: String = name
}

object ASMRegister {
  case object Link extends ASMRegister("Lk")
  case class Local(index: Int) extends ASMRegister(s"R${index}")
  case class Const(index: Int) extends ASMRegister(s"C${index}")

  val locals = (0 until (7 * 32)).map(Local)
  val consts = (0 until (1 * 32)).map(Const)

  val L223 = locals.last
  val C0 = consts(0)
}
