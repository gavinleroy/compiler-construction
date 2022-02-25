package l3

import java.io.PrintWriter
import java.nio.file.{ Files, Paths }

import l3.SymbolicCL3TreeModule.Tree

object Main {
  def main(args: Array[String]): Unit = {
    val backEnd: Tree => TerminalPhaseResult = (
      CL3Interpreter
    )

    val basePath = Paths.get(".").toAbsolutePath
    Either.cond(! args.isEmpty, args.toIndexedSeq, "no input file given")
      .flatMap(L3FileReader.readFilesExpandingModules(basePath, _))
      .flatMap(p => L3Parser.parse(p._1, p._2))
      .flatMap(CL3NameAnalyzer)
      .flatMap(backEnd) match {
        case Right((retCode, maybeMsg)) =>
          maybeMsg foreach println
          sys.exit(retCode)
        case Left(errMsg) =>
          println(s"Error: $errMsg")
          sys.exit(1)
      }
  }

  private lazy val outPrintWriter = new PrintWriter(System.out, true)

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
