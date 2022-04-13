package l3

import java.io.PrintWriter
import java.nio.file.{ Files, Paths }

import l3.SymbolicCL3TreeModule.Tree

import CL3TreeFormatter._ // Implicits required for CL3 tree printing
import CPSTreeFormatter._ // Implicits required for CPS tree printing
import CPSTreeChecker._ // Implicits required for CPS tree checking

object Main {
  def main(args: Array[String]): Unit = {
    val stats = new Statistics()
    val backEnd: Tree => TerminalPhaseResult = (
      CL3ToCPSTranslator
        andThen treePrinter("---------- Before Optimization High")
        andThen CPSOptimizerHigh
        andThen treePrinter("---------- Before value representation")
        andThen CPSValueRepresenter
        andThen treeChecker
        andThen CPSHoister
        andThen CPSOptimizerLow
        andThen treePrinter("---------- After value representation")
        // FIXME remove
        andThen (new CPSInterpreterLow(stats.log _))
    )

    val basePath = Paths.get(".").toAbsolutePath
    Either
      .cond(!args.isEmpty, args.toIndexedSeq, "no input file given")
      .flatMap(L3FileReader.readFilesExpandingModules(basePath, _))
      .flatMap(p => L3Parser.parse(p._1, p._2))
      .flatMap(CL3NameAnalyzer)
      .flatMap(backEnd) match {
      case Right((retCode, maybeMsg)) =>
        maybeMsg foreach println
        println(stats) // FIXME remove
        sys.exit(retCode)
      case Left(errMsg) =>
        println(s"Error: $errMsg")
        sys.exit(1)
    }
  }

  private lazy val outPrintWriter = new PrintWriter(System.out, true)

  private def treeChecker[T <: CPSTreeModule](implicit c: CPSTreeChecker[T]) =
    passThrough(c)

  private def treePrinter[T](msg: String)(implicit f: Formatter[T]): T => T =
    passThrough { tree =>
      outPrintWriter.println(msg)
      f.toDoc(tree).writeTo(80, outPrintWriter)
      outPrintWriter.println()
    }

  private def seqPrinter[T](msg: String): Seq[T] => Seq[T] =
    passThrough { program =>
      outPrintWriter.println(msg)
      program foreach outPrintWriter.println
    }

  private def passThrough[T](f: T => Unit): T => T = { t: T => f(t); t }
}
