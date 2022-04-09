package l3;

import scala.collection.mutable.{ Map => MutableMap }

import SymbolicCPSTreeModuleLow._

final class Statistics {
  private[this] var funCount = 0
  private[this] var cntCount = 0
  private[this] val nodes = MutableMap[Class[_ <: Tree], Int]()
  private[this] val tPrims = MutableMap[Class[_ <: l3.CPSTestPrimitive], Int]()
  private[this] val vPrims = MutableMap[Class[_ <: l3.CPSValuePrimitive], Int]()

  private[this] def inc[K](m: MutableMap[K, Int], k: K): Unit =
    m.put(k, m.getOrElse(k, 0) + 1)

  def nodeCount(cls: Class[_ <: Tree]): Int =
    nodes.getOrElse(cls, 0)

  def testPrimitiveCount(cls: Class[_ <: CPSTestPrimitive]): Int =
    tPrims.getOrElse(cls, 0)

  def valuePrimitiveCount(cls: Class[_ <: CPSValuePrimitive]): Int =
    vPrims.getOrElse(cls, 0)

  def functionsCount = funCount
  def continuationsCount = cntCount

  def log(tree: Tree): Unit = {
    inc(nodes, tree.getClass)

    tree match {
      case LetP(_, p, _, _) =>
        inc(vPrims, p.getClass)
      case LetF(fs, _) =>
        funCount += fs.length
      case LetC(cs, _) =>
        cntCount += cs.length
      case If(p, _, _, _) =>
        inc(tPrims, p.getClass)
      case _ =>
        // nothing to do
    }
  }

  override def toString: String = {
    val sb = new StringBuilder()

    for ((label, map) <- Seq(("Nodes", nodes),
                             ("Value primitives", vPrims),
                             ("Test primitives", tPrims))
         if (map.nonEmpty)) {
      sb ++= (label + "\n" + "=" * label.length + "\n")
      map.toList
        .map { case (c, o) => c.getSimpleName.replace("$","") -> o }
        .sortBy { case (_, o) => -o }
        .foreach { case (c, o) => sb ++= "%,9d  %s\n".format(o, c) }
      sb.append("\n")
    }

    sb ++= "    Functions defined: %,7d\n".format(funCount)
    sb ++= "Continuations defined: %,7d\n".format(cntCount)

    sb.toString
  }
}
