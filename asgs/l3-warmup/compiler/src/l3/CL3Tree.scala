package l3

/**
  * A module for CL₃ trees.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

trait CL3TreeModule {
  type Name
  type Primitive

  sealed abstract class Tree(val pos: Position)
  case class Let(bindings: Seq[(Name, Tree)], body: Tree)
                (implicit pos: Position) extends Tree(pos)
  case class LetRec(functions: Seq[Fun], body: Tree)
                   (implicit pos: Position) extends Tree(pos)
  case class If(cond: Tree, thenE: Tree, elseE: Tree)
               (implicit pos: Position) extends Tree(pos)
  case class App(fun: Tree, args: Seq[Tree])
                (implicit pos: Position) extends Tree(pos)
  case class Prim(prim: Primitive, args: Seq[Tree])
                 (implicit pos: Position) extends Tree(pos)
  case class Halt(arg: Tree)
                 (implicit pos: Position) extends Tree(pos)
  case class Ident(name: Name)
                  (implicit pos: Position) extends Tree(pos)
  case class Lit(value: CL3Literal)
                (implicit pos: Position) extends Tree(pos)

  case class Fun(name: Name, args: Seq[Name], body: Tree)
                (implicit val pos: Position)
}

/**
  * Module for trees after parsing: names and primitives are
  * represented as strings.
  */
object NominalCL3TreeModule extends CL3TreeModule {
  type Name = String
  type Primitive = String
}

/**
  * Module for trees after name analysis: names are represented as
  * symbols (globally-unique names) and primitives as objects.
  */
object SymbolicCL3TreeModule extends CL3TreeModule {
  type Name = Symbol
  type Primitive = L3Primitive
}
