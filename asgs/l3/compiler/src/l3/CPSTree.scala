package l3

/**
  * A module for CPS trees.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

trait CPSTreeModule {
  type Name
  type Literal
  type ValuePrimitive
  type TestPrimitive

  sealed trait Atom extends Product {
    def asName: Option[Name]
    def asLiteral: Option[Literal]
  }
  case class AtomN(n: Name) extends Atom {
    override def asName: Option[Name] = Some(n)
    override def asLiteral: Option[Literal] = None
    override def toString: String = n.toString
  }
  case class AtomL(l: Literal) extends Atom {
    override def asName: Option[Name] = None
    override def asLiteral: Option[Literal] = Some(l)
    override def toString: String = l.toString
  }

  sealed trait Tree
  case class LetP(name: Name, prim: ValuePrimitive, args: Seq[Atom], body:Tree)
      extends Tree
  case class LetC(cnts: Seq[Cnt], body: Tree) extends Tree
  case class LetF(funs: Seq[Fun], body: Tree) extends Tree
  case class AppC(cnt: Name, args: Seq[Atom]) extends Tree
  case class AppF(fun: Atom, retC: Name, args: Seq[Atom]) extends Tree
  case class If(cond: TestPrimitive, args: Seq[Atom], thenC: Name, elseC: Name)
      extends Tree
  case class Halt(arg: Atom) extends Tree

  case class Cnt(name: Name, args: Seq[Name], body: Tree)
  case class Fun(name: Name, retC: Name, args: Seq[Name], body: Tree)
}

/**
  * Module for "high-level" CPS trees: the full L3 literals and
  * primitives are available.
  */
object SymbolicCPSTreeModule extends CPSTreeModule {
  type Name = Symbol
  type Literal = CL3Literal
  type ValuePrimitive = L3ValuePrimitive
  type TestPrimitive = L3TestPrimitive
}

/**
  * Module for "low-level" CPS trees: the only literal values are
  * integers, and the primitives work on integers and/or pointers to
  * heap-allocated blocks.
  */
object SymbolicCPSTreeModuleLow extends CPSTreeModule {
  type Name = Symbol
  type Literal = Bits32
  type ValuePrimitive = CPSValuePrimitive
  type TestPrimitive = CPSTestPrimitive
}
