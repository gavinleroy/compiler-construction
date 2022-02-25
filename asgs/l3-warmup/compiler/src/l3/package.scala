package object l3 {
  type TerminalPhaseResult = Either[String, (Int, Option[String])]

  type L3BlockTag = Int
  type L3Char = Int

  // A 32-bit integer (which could contain a pointer, a tagged value,
  // or an untagged value).
  type Bits32 = Int

  val L3_INT_BITS = java.lang.Integer.SIZE - 1

  // Bit twiddling
  def bitsToIntMSBF(bits: Int*): Int =
    bits.foldLeft(0) { (v, b) => (v << 1) | b }

  def fitsInNSignedBits(bits: Int)(value: Int): Boolean = {
    require(0 <= bits && bits < Integer.SIZE)
    val value1 = value >> (bits - 1)
    value1 == 0 || value1 == -1
  }

  def fitsInNUnsignedBits(bits: Int)(value: Int): Boolean = {
    require(0 <= bits && bits < Integer.SIZE)
    (value >>> bits) == 0
  }

  // Substitutions
  type Subst[T] = Map[T, T]
  def emptySubst[T]: Subst[T] =
    Map.empty[T, T].withDefault(identity)
  def subst[T](from: T, to: T): Subst[T] =
    emptySubst[T] + (from -> to)
  def subst[T](from: Seq[T], to: Seq[T]): Subst[T] =
    emptySubst[T] ++ (from zip to)

  // Fixed point computation
  private def fixedPoint[T](start: T, maxIt: Option[Int])(f: T=>T): T = {
    val approx = LazyList.iterate(start, maxIt getOrElse Integer.MAX_VALUE)(f)
    val (improv, stable) = ((approx zip approx.tail) span (p => p._1 != p._2))
    if (improv.isEmpty) stable.head._1 else improv.last._2
  }

  private[l3] def fixedPoint[T](start: T)(f: T=>T): T =
    fixedPoint(start, None)(f)

  private[l3] def fixedPoint[T](start: T, maxIt: Int)(f: T=>T): T =
    fixedPoint(start, Some(maxIt))(f)
}
