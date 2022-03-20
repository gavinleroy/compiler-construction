package l3

/**
  * A class for value-producing primitives.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

sealed abstract class CPSValuePrimitive(val name: String) {
  override def toString: String = name
}

object CPSValuePrimitive {
  case object Add extends CPSValuePrimitive("+")
  case object Sub extends CPSValuePrimitive("-")
  case object Mul extends CPSValuePrimitive("*")
  case object Div extends CPSValuePrimitive("/")
  case object Mod extends CPSValuePrimitive("%")

  case object ShiftLeft extends CPSValuePrimitive("shift-left")
  case object ShiftRight extends CPSValuePrimitive("shift-right")
  case object And extends CPSValuePrimitive("and")
  case object Or extends CPSValuePrimitive("or")
  case object XOr extends CPSValuePrimitive("xor")

  case object ByteRead extends CPSValuePrimitive("byte-read")
  case object ByteWrite extends CPSValuePrimitive("byte-write")

  case class BlockAlloc(tag: L3BlockTag)
      extends CPSValuePrimitive(s"block-alloc-${tag}")
  case object BlockTag extends CPSValuePrimitive("block-tag")
  case object BlockLength extends CPSValuePrimitive("block-length")
  case object BlockGet extends CPSValuePrimitive("block-get")
  case object BlockSet extends CPSValuePrimitive("block-set!")

  case object Id extends CPSValuePrimitive("id")
}

/**
  * A class for testing primitives.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

sealed abstract class CPSTestPrimitive(val name: String) {
  override def toString: String = name
}

object CPSTestPrimitive {
  case object Lt extends CPSTestPrimitive("<")
  case object Le extends CPSTestPrimitive("<=")
  case object Eq extends CPSTestPrimitive("=")
}
