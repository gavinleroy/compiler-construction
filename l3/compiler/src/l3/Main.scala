package l3

import java.io.PrintWriter
import java.nio.file.{ Files, Paths }

import l3.SymbolicCL3TreeModule.Tree

import CL3TreeFormatter._ // Implicits required for CL3 tree printing
import CPSTreeFormatter._ // Implicits required for CPS tree printing
import CPSTreeChecker._ // Implicits required for CPS tree checking

object Main {
  def main(args: Array[String]): Unit = {
    val backEnd: Tree => TerminalPhaseResult = (
      // CL3Interpreter
      CL3ToCPSTranslator
      // andThen treePrinter("---------- After translation to CPS")
        andThen CPSContifier
        // andThen treePrinter("---------- After contification")
        andThen CPSOptimizerHigh
        // andThen treePrinter("---------- After high optimization")
        // andThen CPSInterpreterHigh
        andThen CPSValueRepresenter
        // andThen treePrinter("---------- After value representation")
        andThen CPSHoister
        // andThen treePrinter("---------- After hoisting")
        andThen CPSOptimizerLow
        // andThen treePrinter("---------- After low optimization")
        // andThen CPSInterpreterLow
        andThen CPSConstantNamer
        // andThen treePrinter("---------- After constant naming")
        andThen CPSRegisterAllocator
        // andThen treePrinter("---------- After register allocation")
        andThen CPSToASMTranslator
        // andThen seqPrinter("---------- After translation to assembly")
        // andThen ASMToCTranslator(Option(System.getProperty("l3.out-c-file"))
        //                            .getOrElse("out.c"))
        andThen ASMLabelResolver
        // andThen seqPrinter("---------- After label resolution")
        // andThen ASMInterpreter
        andThen ASMFileWriter(
          Option(System.getProperty("l3.out-asm-file"))
            .getOrElse("out.l3a")
        )
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
