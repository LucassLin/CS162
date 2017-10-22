package miniprolog.parser

import miniprolog.syntax.lowlevel._
import miniprolog.syntax.highlevel._

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.syntactical._

// responsible for parsing high-level syntax
object Parser extends StandardTokenParsers with PackratParsers {
  type P[T] = PackratParser[T]

  lexical.reserved += ("true", "fail", "write", "not", "is")

  lexical.delimiters += (",", ";", "=", ":-", "(", ")", ".", "[", "]", "|",
                         ">", "<", "=<", ">=", "=:=", "=/=",
                         "+", "-", "*", "/")

  def identWithFirstChar(msg: String, pred: Char => Boolean): P[String] = {
    import lexical.Identifier
    elem(msg,
         _ match {
           case Identifier(chars) => {
             assert(chars.length > 0)
             pred(chars.charAt(0))
           }
           case _ => false
         }) ^^ (_.chars)
  }

  def varIdent(): P[String] =
    identWithFirstChar("var identifier",
                       c => c == '_' || (c.isLetter && c.isUpper))

  def atomIdent(): P[String] =
    identWithFirstChar("atom identifer",
                       c => c.isLetter && !c.isUpper)
      
  lazy val varP: P[FullVar] =
    varIdent ^^ { case name => FullVar(name) }

  lazy val atomP: P[FullAtom] =
    atomIdent ^^ { case kind => FullAtom(Symbol(kind)) }

  lazy val relationalTermP: P[FullRelationalTerm] =
    (varP ^^ (FullExpressionVar)) | (numP ^^ (FullExpressionNum))

  lazy val expressionBinopP: P[FullExpressionBinop] =
    exprP ~ bopP ~ exprP ^^ { case e1 ~ op ~ e2 => FullExpressionBinop(e1, op, e2) }

  lazy val exprP: P[FullExpressionTerm] =
    // all relational terms are also expresison terms; the type system cannot
    // figure this out
    ("(" ~> exprP <~ ")") | expressionBinopP | (relationalTermP ^^ (_.asInstanceOf[FullExpressionTerm]))

  lazy val bopP: P[ArithOp] =
    ("+" ^^^ ArithPlus) |
    ("-" ^^^ ArithMinus) |
    ("*" ^^^ ArithTimes) |
    ("/" ^^^ ArithDiv)

  lazy val relationalOpP: P[RelationalOp] =
    ("<" ^^^ LT) |
    ("=<" ^^^ LTE) |
    (">" ^^^ GT) |
    (">=" ^^^ GTE) |
    ("=:=" ^^^ EQ) |
    ("=/=" ^^^ NEQ)

  lazy val functorP: P[FullFunctor] =
    atomP ~ ("(" ~> repsep(termExpP, ",") <~ ")") ^^
      { case name ~ params => FullFunctor(name, params) }
  
  lazy val infixFunctorP: P[FullFunctor] =
    termExpP ~ atomP ~ termExpP ^^
      { case param1 ~ name ~ param2 => FullFunctor(name, List(param1, param2)) }

  lazy val listP: P[FullTermExp] =
    "[" ~> (termDestructP | termListP) <~ "]" ^^ { case res => res }

  lazy val termListP: P[TermList] = 
    repsep(termExpP, ",") ^^ { case terms => TermList(terms) }

  lazy val termDestructP: P[TermListDestruct] = 
    termExpP ~ ("|" ~> termExpP) ^^ { case head ~ tail => TermListDestruct(head, tail) }

  lazy val termFunctorP: P[FullTermFunctor] =
    functorP ^^ (FullTermFunctor)

  lazy val numP: P[FullTermNum] =
    (numericLit ^^ (n => FullTermNum(n.toInt))) |
    ("-" ~> numericLit ^^ (n => FullTermNum(-n.toInt)))

  lazy val termExpP: P[FullTermExp] =
    termFunctorP | varP | atomP | numP | listP
  
  lazy val orP: P[FullOr] =
    bodyP ~ (";" ~> bodyP) ^^ { case b1 ~ b2 => FullOr(b1, b2) }

  lazy val andP: P[FullAnd] =
    bodyP ~ ("," ~> bodyP) ^^ { case a1 ~ a2 => FullAnd(a1, a2) }

  lazy val unifyP: P[FullUnify] = 
    termExpP ~ ("=" ~> termExpP) ^^ { case te1 ~ te2 => FullUnify(te1, te2) }

  lazy val callP: P[FullCall] = 
    (infixFunctorP | functorP) ^^ { case fun => FullCall(fun) }

  lazy val writeP: P[FullWrite] =
    ("write" ~ "(") ~> varP <~ ")" ^^ { case v => FullWrite(v) }

  lazy val trueP: P[FullBody] = 
    "true" ^^^ (FullTrue)

  lazy val failP: P[FullBody] =
    "fail" ^^^ (FullFail)

  lazy val compareP: P[FullCompare] =
    relationalTermP ~ relationalOpP ~ relationalTermP ^^ { case rt1 ~ op ~ rt2 => FullCompare(rt1, op, rt2) }

  lazy val arithmeticP: P[FullArithmetic] =
    relationalTermP ~ ("is" ~> expressionBinopP) ^^ { case assignTo ~ expr => FullArithmetic(assignTo, expr) }

  lazy val bodyP: P[FullBody] =
    andP | orP | trueP | failP | unifyP | compareP | arithmeticP | writeP | callP | ("(" ~> bodyP <~ ")")

  lazy val clauseP: P[FullClause] =
    functorP ~ opt(":-" ~> bodyP) <~ "." ^^ { case fun ~ body => FullClause(fun, body.getOrElse(FullTrue)) }

  lazy val queryP: P[FullQuery] =
    bodyP <~ "." ^^ { case b => FullQuery(b) }

  def main(args: Array[String]) {
    if (args.length != 1) {
      println("Needs a file to parse")
    } else {
      import scala.io._
      println(getAst(Source.fromFile(args(0)).mkString))
    }
  }

  def parseQuery(query: String): FullQuery = {
    val lexer = new lexical.Scanner(query)
    val result = phrase(queryP)(lexer)
    result match {
      case Success(ast, _) => ast
      case NoSuccess(msg, next) => {
        println( "Parse error: " + msg )
        println( "At line " + next.pos.line + ", column " + next.pos.column )
        println( next.pos.longString )
        sys.exit(1)
      }
    }
  }

  def stripComments(prog: String): String =
    prog.split("\n").map(str => {
      val index = str.indexOf('%')
      if (index != -1) {
        str.substring(0, index)
      } else {
        str
      }
    }).mkString("\n")

  def getAst(prog: String): List[FullClause] = {
    // parse the program
    val lexer = new lexical.Scanner(stripComments(prog))
    val result = phrase(rep(clauseP))(lexer)

    // return result or a useful error message
    result match {
      case Success(ast, _) => ast
      case NoSuccess(msg, next) => {
        println( "Parse error: " + msg )
        println( "At line " + next.pos.line + ", column " + next.pos.column )
        println( next.pos.longString )
        sys.exit(1)
      }
    }
  }
}
