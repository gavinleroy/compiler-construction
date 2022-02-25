package l3

import java.io.{ ByteArrayOutputStream, PrintStream }
import java.nio.file.{ Paths }

import scala.util.Using.{resource => using}

import SymbolicCL3TreeModule.Tree

object L3Tester {
  def compile[T](backEnd: Tree => Either[String, T])
             (inFileNames: Seq[String]): Either[String, T] = {
    val basePath = Paths.get(".").toAbsolutePath.normalize
    Right(inFileNames)
      .flatMap(L3FileReader.readFilesExpandingModules(basePath, _))
      .flatMap(p => L3Parser.parse(p._1, p._2))
      .flatMap(CL3NameAnalyzer)
      .flatMap(backEnd)
  }

  def compileNoFail[T](backEnd: Tree => T)
                   (inFileNames: Seq[String]): Either[String, T] =
    compile(t => Right(backEnd(t)))(inFileNames)

  def compileAndRun(backEnd: Tree => TerminalPhaseResult)
                   (inFileNames: Seq[String]): Either[String, String] = {
    def outputCapturingBackend(t: Tree): Either[String, String] = {
      val outBS = new ByteArrayOutputStream()
      using(new PrintStream(outBS)) { outPS =>
        val out0 = System.out
        try {
          System.setOut(outPS)
          backEnd(t)
            .flatMap(_ => Right(outBS.toString("UTF-8")))
        } finally {
          System.setOut(out0)
        }
      }
    }

    compile(outputCapturingBackend(_))(inFileNames)
  }

  val backEnd1 = (
    CL3Interpreter
  )
}
