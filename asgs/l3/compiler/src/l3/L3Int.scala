package l3

final class L3Int private(private val v: Int) extends AnyVal {
  def toInt: Int = v

  def +(that: L3Int): L3Int = L3Int.ofIntClipped(this.v + that.v)
  def -(that: L3Int): L3Int = L3Int.ofIntClipped(this.v - that.v)
  def *(that: L3Int): L3Int = L3Int.ofIntClipped(this.v * that.v)
  def /(that: L3Int): L3Int = L3Int.ofIntClipped(this.v / that.v)
  def %(that: L3Int): L3Int = L3Int.ofIntClipped(this.v % that.v)
  def &(that: L3Int): L3Int = L3Int.ofIntClipped(this.v & that.v)
  def |(that: L3Int): L3Int = L3Int.ofIntClipped(this.v | that.v)
  def ^(that: L3Int): L3Int = L3Int.ofIntClipped(this.v ^ that.v)
  def <<(that: L3Int): L3Int = L3Int.ofIntClipped(this.v << that.v)
  def >>(that: L3Int): L3Int = L3Int.ofIntClipped(this.v >> that.v)

  def <(that: L3Int): Boolean = this.v < that.v
  def <=(that: L3Int): Boolean = this.v <= that.v
  def >(that: L3Int): Boolean = this.v > that.v
  def >=(that: L3Int): Boolean = this.v >= that.v

  override def toString: String = v.toString
}

object L3Int {
  private def ofIntClipped(v: Int): L3Int =
    L3Int((v << 1) >> 1)

  def canConvertFromInt(i: Int): Boolean =
    fitsInNSignedBits(L3_INT_BITS)(i)

  def canConvertFromIntUnsigned(i: Int): Boolean =
    fitsInNUnsignedBits(L3_INT_BITS)(i)

  def ofIntUnsigned(v: Int): L3Int = {
    require(canConvertFromIntUnsigned(v))
    new L3Int((v << 1) >> 1)
  }

  def apply(v: Int): L3Int = {
    require(canConvertFromInt(v))
    new L3Int(v)
  }

  def unapply(v: L3Int): Option[Int] =
    Some(v.toInt)
}
