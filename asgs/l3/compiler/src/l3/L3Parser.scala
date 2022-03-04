package l3

import fastparse._
import NominalCL3TreeModule._

/**
  * Parsing (including lexical analysis) for the L₃ language.
  *
  * @author Michel Schinz <Michel.Schinz@epfl.ch>
  */

object L3Parser {
  def parse(programText: String,
            indexToPosition: Int => Position): Either[String, Tree] = {
    val parser = new S(indexToPosition)
    fastparse.parse(programText, parser.program(_)) match {
      case Parsed.Success(program, _) =>
        Right(program)
      case Parsed.Failure(lp, index, _) =>
        Left(s"${indexToPosition(index)}: parse error (expected: $lp)")
    }
  }

  // Lexical analysis (for which whitespace is significant)
  private class L(indexToPosition: Int => Position) {
    import NoWhitespace._
    private implicit val indexToPositionView = indexToPosition

    // Literals
    private def sign[_: P] = P(CharIn("+\\-"))
    private def prefix2[_: P] = IgnoreCase("#b")
    private def prefix16[_: P] = IgnoreCase("#x")
    private def digit2[_: P] = CharIn("0-1")
    private def digit10[_: P] = CharIn("0-9")
    private def digit16[_: P] = CharIn("0-9a-fA-F")
    private def unicodeChar[_: P] = P(
      CharPred(!Character.isHighSurrogate(_))
        | (CharPred(Character.isHighSurrogate)
             ~ CharPred(Character.isLowSurrogate)))

    private def integer2[_: P] = P(
      (prefix2 ~/ digit2.rep(1).!)
        .map { Integer.parseInt(_, 2) }
        .filter { L3Int.canConvertFromIntUnsigned(_) }
        .map { L3Int.ofIntUnsigned(_) })
    private def integer16[_: P] = P(
      (prefix16 ~/ digit16.rep(1).!)
        .map { Integer.parseInt(_, 16) }
        .filter { L3Int.canConvertFromIntUnsigned(_) }
        .map { L3Int.ofIntUnsigned(_) })
    private def integer10[_: P] = P(
      (sign.? ~ digit10 ~/ digit10.rep).!
        .map { Integer.parseInt(_, 10) }
        .filter { L3Int.canConvertFromInt(_) })
      .map { L3Int(_) }
    private def integer[_: P] = P(
      (Index ~ (integer2 | integer10 | integer16))
        .map { case (i, v) => Lit(IntLit(v))(i) })
    private def string[_: P] = P(
      (Index ~ "\"" ~/ CharPred(c => c != '\n' && c != '"').rep.! ~ "\"")
        .map { case (i, s) => sStringLit(s)(i) })
    private def char[_: P] = P(
      (Index ~ "'" ~/ unicodeChar.! ~ "'")
        .map { case (i, c) => Lit(CharLit(c.codePointAt(0)))(i) })
    private def bool[_: P] = P(
      (Index ~ StringIn("#t", "#f").!)
        .map { case (i, v) => Lit(BooleanLit(v == "#t"))(i) })
    private def unit[_: P] = P(
      (Index ~ "#u")
        .map { case i => Lit(UnitLit)(i) })

    def literal[_: P] = P(integer | string | char | bool | unit)

    // Identifiers
    private def identStart[_: P] = P(CharIn("|!%&*+\\-./:<=>?^_~a-zA-Z"))
    private def identCont[_: P] = P(identStart | digit10)
    private def identSuffix[_: P] = P("@" ~ digit10.rep(1))

    def identStr[_: P] = P(
      (identStart ~/ identCont.rep ~/ identSuffix.?).!)
    def identifier[_: P] = P(
      (Index ~ identStr).map { case (i, n) => Ident(n)(i) })

    // Keywords
    def kDef[_: P] = P("def" ~ !identCont)
    def kDefrec[_: P] = P("defrec" ~ !identCont)
    def kFun[_: P] = P("fun" ~ !identCont)
    def kLet[_: P] = P("let" ~ !identCont)
    def kLet_*[_: P] = P("let*" ~ !identCont)
    def kLetrec[_: P] = P("letrec" ~ !identCont)
    def kRec[_: P] = P("rec" ~ !identCont)
    def kBegin[_: P] = P("begin" ~ !identCont)
    def kCond[_: P] = P("cond" ~ !identCont)
    def kIf[_: P] = P("if" ~ !identCont)
    def kAnd[_: P] = P("and" ~ !identCont)
    def kOr[_: P] = P("or" ~ !identCont)
    def kNot[_: P] = P("not" ~ !identCont)
    def kHalt[_: P] = P("halt" ~ !identCont)
    def kPrim[_: P] = P("@")
  }

  // Syntactic analysis (for which whitespace and comments are ignored)
  private class S(indexToPosition: Int => Position) {
    val lexer = new L(indexToPosition)
    import lexer._

    private implicit val whitespace = { implicit ctx: ParsingRun[_] =>
      import NoWhitespace._
      (CharIn(" \t\n\r")
         | (";" ~ CharPred(c => c != '\n' && c != '\r').rep)).rep
    }
    private implicit val indexToPositionView = indexToPosition

    def program[_: P]: P[Tree] =
      P("" ~ topExpr ~ End) // The initial "" allows leading whitespace

    private def topExpr[_: P]: P[Tree] = P(defP | defrecP | exprP)

    private def defP[_: P] = P(
      (iPar(kDef ~ identStr ~ expr) ~ topExpr)
        .map { case (i, (n, v), p) => Let(Seq((n, v)), p)(i) })
    private def defrecP[_: P] = P(
      (iPar(kDefrec ~ identStr ~ anonFun) ~ topExpr)
        .map { case (i, (n, (a, b)), p) =>
          LetRec(Seq(Fun(n, a, b)(i)), p)(i) })
    private def exprP[_: P] = P(
      (ix(expr ~ topExpr.?))
        .map { case (i, (e, p)) => sBegin(e +: p.toSeq)(i) })

    private def expr[_: P]: P[Tree] = P(
      fun | let | let_* | letrec | rec | begin | cond | if_ | and | or | not
        | halt | app | prim | literal | identifier)
    private def exprs[_: P] = expr.rep
    private def iExprs[_: P] = ix(exprs)
    private def exprs1[_: P] = expr.rep(1)
    private def iExprs1[_: P] = ix(exprs1)

    private def anonFun[_: P] = P(
      par("fun" ~ par(identStr.rep) ~ iExprs1)
        .map { case (a, (i, e)) => (a, sBegin(e)(i)) })
    private def funDef[_: P] = P(
      iPar(identStr ~ anonFun)
        .map { case (i, (n, (a, e))) => Fun(n, a, e)(i) })
    private def binding[_: P] = P(
      par(identStr ~ expr)
        .map { case (i, e) => (i, e) })
    private def bindings[_: P] = P(
      par(binding.rep))

    private def fun[_: P] = P(
      ix(anonFun)
        .map { case (i, (a, e)) => sFun(a, e)(i) })
    private def let[_: P] = P(
      iPar(kLet ~/ bindings ~ iExprs1)
        .map { case (i1, (b, (i2, e))) => Let(b, sBegin(e)(i2))(i1) })
    private def let_*[_: P] = P(
      iPar(kLet_* ~/ bindings ~ iExprs1)
        .map { case (i1, (b, (i2, e))) => sLet_*(b, sBegin(e)(i2))(i1) })
    private def letrec[_: P]= P(
      iPar(kLetrec ~/ par(funDef.rep) ~ iExprs1)
        .map { case (i1, (f, (i2, e))) => LetRec(f, sBegin(e)(i2))(i1) })
    private def rec[_: P] = P(
      iPar(kRec ~/ identStr ~ bindings ~ iExprs1)
        .map { case (i1, (n, b, (i2, e))) => sRec(n, b, sBegin(e)(i2))(i1) })
    private def begin[_: P] = P(
      iPar(kBegin ~/ exprs1)
        .map { case (i, e) => sBegin(e)(i) })

    private def cond[_: P] = P(
      iPar(kCond ~/ par(expr ~ exprs1).rep(1))
        .map { case (i, a) => sCond(a)(i) })
    private def if_[_: P] = P(
      iPar(kIf ~ expr ~ expr ~ expr.?)
        .map { case (i, (c, t, f)) =>
          If(c, t, f.getOrElse(Lit(UnitLit)(i)))(i) })
    private def and[_: P] = P(
      iPar(kAnd ~/ expr.rep(2))
        .map { case (i, es) => sAnd(es)(i) })
    private def or[_: P] = P(
      iPar(kOr ~/ expr.rep(2))
        .map { case (i, es) => sOr(es)(i) })
    private def not[_: P] = P(
      iPar(kNot ~/ expr)
        .map { case (i, e) => sNot(e)(i) })

    private def app[_: P] = P(
      iPar(expr ~ exprs)
        .map { case (i, (e, es)) => App(e, es)(i) })
    private def prim[_: P] = P(
      iPar(kPrim ~/ identStr ~ exprs)
        .map { case (i, (p, es)) => Prim(p, es)(i) })
    private def halt[_: P] = P(
      iPar(kHalt ~/ expr)
        .map { case (i, e) => Halt(e)(i) })

    private def par[T, _: P](b: =>P[T]): P[T] = P("(" ~ b ~ ")")
    private def ix[T, _: P](b: =>P[T]): P[(Int, T)] = Index ~ b
    private def iPar[T, _: P](b: =>P[T]): P[(Int, T)] = ix(par(b))
  }

  // Syntactic sugar translation.
  private var freshCounter = 0
  private def freshName(prefix: String): String = {
    freshCounter += 1
    prefix + "$" + freshCounter
  }

  private def sFun(args: Seq[String], body: Tree)
                  (implicit p: Position): Tree = {
    val fName = freshName("fun")
    LetRec(Seq(Fun(fName, args, body)), Ident(fName))
  }
  private def sLet_*(bdgs: Seq[(String,Tree)], body: Tree)
                    (implicit p: Position): Tree =
    bdgs.foldRight(body)((b, t) => Let(Seq(b), t))
  private def sBegin(exprs: Seq[Tree])(implicit p: Position): Tree =
    exprs reduceRight { (e1, e2) => Let(Seq((freshName("begin"), e1)), e2) }
  private def sRec(name: String, bdgs: Seq[(String, Tree)], body: Tree)
                  (implicit p: Position) =
    LetRec(Seq(Fun(name, bdgs map { _._1 }, body)),
           App(Ident(name), bdgs map { _._2 }))
  private def sAnd(es: Seq[Tree])(implicit p: Position): Tree =
    es reduceRight { If(_, _, Lit(BooleanLit(false))) }
  private def sOr(es: Seq[Tree])(implicit p: Position): Tree = {
    es reduceRight { (e, r) =>
      val en = freshName("or")
      Let(Seq((en, e)), If(Ident(en), Ident(en), r))
    }
  }
  private def sNot(e: Tree)(implicit p: Position): Tree =
    If(e, Lit(BooleanLit(false)), Lit(BooleanLit(true)))
  private def sCond(clses: Seq[(Tree, Seq[Tree])])(implicit p: Position): Tree =
    clses.foldRight(Lit(UnitLit) : Tree){ case ((c, t), e) =>
      If(c, sBegin(t), e) }
  private def sStringLit(s: String)(implicit p: Position): Tree = {
    val b = freshName("string")
    val cs = codePoints(s)
    Let(Seq((b, Prim("block-alloc-"+ BlockTag.String.id,
                     Seq(Lit(IntLit(L3Int(cs.length))))))),
        sBegin((cs.zipWithIndex map {case (c, i) =>
                  Prim("block-set!",
                       Seq(Ident(b), Lit(IntLit(L3Int(i))), Lit(CharLit(c)))) })
                 :+ Ident(b)))
  }

  private def codePoints(chars: Seq[Char]): Seq[L3Char] = chars match {
    case Seq(h, l, r @ _*) if (Character.isSurrogatePair(h, l)) =>
      Character.toCodePoint(h, l) +: codePoints(r)
    case Seq(c, r @ _*) =>
      c.toInt +: codePoints(r)
    case Seq() =>
      Seq()
  }
}
