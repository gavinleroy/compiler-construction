package l3

import java.io.{ ByteArrayInputStream }
import java.nio.file.{ Files, Paths, Path }
import java.nio.charset.StandardCharsets.UTF_8

import scala.util.Using.{resource => using}

import utest._

import SymbolicCL3TreeModule.Tree

trait ExamplesTests {
  val backEnd: Tree => TerminalPhaseResult

  def compileAndRun(fileName: String, input: String): Either[String, String] = {
    using(new ByteArrayInputStream(input.getBytes(UTF_8))) { inS =>
      val in0 = System.in
      try {
        System.setIn(inS)
        L3Tester.compileAndRun(backEnd)(Seq(fileName))
      } finally {
        System.setIn(in0)
      }
    }
  }

  def readFile(fileName: String): String =
    new String(Files.readAllBytes(Paths.get(fileName)), UTF_8)

  def testExpectedOutput(implicit path: utest.framework.TestPath) = {
    val testName = path.value.last
    val input = readFile(s"../tests/${testName}.in")
    val expectedOut = readFile(s"../tests/${testName}.out")
    assertMatch(compileAndRun(s"../examples/${testName}.l3m", input)) {
      case Right(s: String) if s == expectedOut =>
    }
  }

  val tests = Tests {
    // Note: sudoku is too slow to be included here
    test("bignums") { testExpectedOutput }
    test("maze") { testExpectedOutput }
    test("queens") { testExpectedOutput }
    test("unimaze") { testExpectedOutput }
  }
}

object ExamplesTests1 extends TestSuite with ExamplesTests {
  val backEnd = L3Tester.backEnd1
}
