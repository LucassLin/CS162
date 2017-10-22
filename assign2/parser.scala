package simplescala.interpreter

import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StdTokenParsers

case class ParseWithExistingResult(newDefs: Map[FunctionName, Def],
                                   overwritten: Set[FunctionName])

// The parsing code below handles the parsing of programs (needed
// for normal execution) and values (needed for parsing the
// expected results of tests)

// Parsing challenges:
// 1.) Tuples look like expressions in parentheses.
//     Tuples always have length 2.
// 2.) e1(e2) is difficult to parse, because it overlaps
//     with fn(e) and cn(e).  cn is easy to separate out,
//     because we require constructors to start with
//     a captial letter.  As for the defs, we will do a later
//     pass looking for cases of x(e), and if the name of x is
//     one of the function names, we will replace it with a function
//     call node
object SimpleScalaParser extends StdTokenParsers with PackratParsers {
  import scala.util.parsing.combinator.lexical.StdLexical

  type P[+T] = PackratParser[T]
  type Error = String
  type Tokens = StdLexical

  val lexical = new StdLexical
  lexical.delimiters ++= Seq("(", ")", "{", "}", ",", "=>",
                             "+", "-", "*", "/", "&&", "||",
                             "=", "<", "<=", "._", ";;;")
  lexical.reserved ++= Seq("unit", "if", "else", "match", "case", "val", "def",
                           "true", "false", "STUCK")

  lazy val upperCaseIdent: P[String] = ident.flatMap(i => {
    val isUpper = (c: Char) => ('A' to 'Z').contains(c)
    if (isUpper(i.charAt(0)))
      success(i)
    else
      failure("unexpected lowercase letter")
  })

  lazy val notUpperCaseIdent: P[String] = ident.flatMap(i => {
    val isUpper = (c: Char) => ('A' to 'Z').contains(c)
    if (!isUpper(i.charAt(0)))
      success(i)
    else
      failure("unexpected lowercase letter")
  })

  lazy val variable: P[Variable] =
    notUpperCaseIdent ^^ Variable.apply

  lazy val string: P[String] = stringLit

  lazy val boolean: P[Boolean] =
    ("true" ^^^ true) |
    ("false" ^^^ false)

  lazy val integer: P[Int] =
    numericLit ^^ (i => i.toInt)

  lazy val nat: P[Nat] = numericLit.flatMap(s => {
    val i = s.toInt
    if (i > 0) {
      success(Nat(i))
    } else {
      failure("not a positive natural number")
    }
  })

  // function names will be handled in a later pass

  lazy val constructorName: P[ConstructorName] =
    upperCaseIdent ^^ ConstructorName.apply

  lazy val multDiv: P[Binop] =
    "*" ^^^ BinopTimes |
    "/" ^^^ BinopDiv

  lazy val primExp: P[Exp] =
    ("unit" ^^^ UnitExp |
     string ^^ StringExp.apply |
     boolean ^^ BooleanExp.apply |
     integer ^^ IntExp.apply |
     matchExp |
     functionExp |
     anonCallExp | // function exps handled in second pass
     ifExp |
     blockExp |
     accessExp |
     tupleExp |
     constructorExp |
     variable ^^ VariableExp.apply |
     ("(" ~> exp <~ ")"))

  lazy val multDivExp: P[Exp] =
    (primExp ~ multDiv ~ primExp ^^ { case e1 ~ op ~ e2 => BinopExp(e1, op, e2) }) |
    primExp

  lazy val plusMinus: P[Binop] =
    "+" ^^^ BinopPlus |
    "-" ^^^ BinopMinus

  lazy val plusMinusExp: P[Exp] =
    (multDivExp ~ plusMinus ~ multDivExp ^^ { case e1 ~ op ~ e2 => BinopExp(e1, op, e2) }) |
    multDivExp

  lazy val lessLessThan: P[Binop] =
     "<=" ^^^ BinopLTE |
     "<" ^^^ BinopLT

  lazy val lessLessThanExp: P[Exp] =
    (plusMinusExp ~ lessLessThan ~ plusMinusExp ^^ { case e1 ~ op ~ e2 => BinopExp(e1, op, e2) }) |
    plusMinusExp

  lazy val andExp: P[Exp] =
    (lessLessThanExp ~ "&&" ~ lessLessThanExp ^^ { case e1 ~ _ ~ e2 => BinopExp(e1, BinopAnd, e2) }) |
    lessLessThanExp

  lazy val orExp: P[Exp] =
    (andExp ~ "||" ~ andExp ^^ { case e1 ~ _ ~ e2 => BinopExp(e1, BinopOr, e2) }) |
    andExp

  lazy val functionExp: P[FunctionExp] =
    variable ~ ("=>" ~> exp) ^^ { case x ~ e => FunctionExp(x, e) }

  lazy val anonCallExp: P[AnonCallExp] =
    exp ~ ("(" ~> exp <~ ")") ^^ { case e1 ~ e2 => AnonCallExp(e1, e2) }

  lazy val ifExp: P[IfExp] =
    "if" ~ "(" ~ exp ~ ")" ~ exp ~ "else" ~ exp ^^
    { case _ ~ _ ~ e1 ~ _ ~ e2 ~ _ ~ e3 => IfExp(e1, e2, e3) }

  lazy val valval: P[Val] =
    "val" ~> variable ~ ("=" ~> exp) ^^
    { case x ~ e => Val(x, e) }

  lazy val blockExp: P[BlockExp] =
    "{" ~> rep1(valval) ~ exp <~ "}" ^^
    { case vals ~ e => BlockExp(vals, e) }

  def tupleLike[A, B](inner: => P[A], f: List[A] => B): P[B] = {
    ("(" ~> rep1sep(inner, ",") <~ ")").flatMap(elems => {
      if (elems.size >= 2) {
        success(f(elems))
      } else {
        failure("tuples must contain at least two elements")
      }
    })
  }

  lazy val tupleExp: P[TupleExp] =
    tupleLike(exp, TupleExp.apply)

  lazy val accessExp: P[AccessExp] =
    exp ~ ("._" ~> nat) ^^ { case e ~ n => AccessExp(e, n) }

  def constructorLike[A, B](inner: => P[A], f: (ConstructorName, A) => B): P[B] = {
    constructorName ~ ("(" ~> inner <~ ")") ^^
    { case cn ~ a => f(cn, a) }
  }

  lazy val constructorExp: P[ConstructorExp] =
    constructorLike(exp, ConstructorExp.apply)

  lazy val constructorCase: P[ConstructorCase] =
    ("case" ~> constructorName) ~ ("(" ~> variable <~ ")") ~ ("=>" ~> exp) ^^
    { case cn ~ x ~ e => ConstructorCase(cn, x, e) }

  lazy val tupCase: P[TupCase] =
    ("case" ~> tupleLike(variable, (l: List[Variable]) => l) <~ "=>") ~ exp ^^
    { case xs ~ e => TupCase(xs, e) }

  lazy val casecase: P[Case] =
    constructorCase | tupCase

  lazy val matchExp: P[MatchExp] =
    exp ~ "match" ~ "{" ~ rep1(casecase) ~ "}" ^^
    { case e ~ _ ~ _ ~ cases ~ _ => MatchExp(e, cases) }

  lazy val exp: P[Exp] = orExp

  lazy val defdef: P[Def] =
    "def" ~ notUpperCaseIdent ~ "(" ~ variable ~ ")" ~ "=" ~ exp ^^
    { case _ ~ fn ~ _ ~ x ~ _ ~ _ ~ e => Def(FunctionName(fn), x, e) }

  def duplicates[A](as: Seq[A]): Seq[A] =
    as.groupBy(n => n).values.filter(_.tail.nonEmpty).map(_.head).toSeq

  lazy val defs: P[List[Def]] =
    rep(defdef).flatMap(defs => {
      val dups = duplicates(defs.toSeq.map(_.fn.name))
      if (dups.isEmpty) {
        success(defs)
      } else {
        failure("duplicate function names: " + dups.mkString(", "))
      }
    })
  lazy val program: P[Program] =
    defs ~ exp ^^
    { case thedefs ~ e => functionCallPass(thedefs, e) }

  def functionCallPass(defs: List[Def]): (Set[String], List[Def]) = {
    val functionNames = defs.map(_.fn.name).toSet
    (functionNames, defs.map(d => functionCallPass(functionNames, d)))
  }

  def functionCallPass(defs: List[Def], e: Exp): Program = {
    val (functionNames, newDefs) = functionCallPass(defs)
    Program(newDefs,
            functionCallPass(functionNames, e))
  }

  def functionCallPass(functionNames: Set[String], defdef: Def): Def = {
    Def(defdef.fn, defdef.x, functionCallPass(functionNames, defdef.e))
  }

  def functionCallPass(functionNames: Set[String], v: Val): Val = {
    v.copy(e = functionCallPass(functionNames, v.e))
  }

  def functionCallPass(functionNames: Set[String], vs: List[Val]): List[Val] = {
    vs.map(v => functionCallPass(functionNames, v))
  }

  def functionCallPass(functionNames: Set[String], e: Exp): Exp = {
    def recCase(theCase: Case): Case = {
      theCase match {
        case ConstructorCase(cn, x, e) => ConstructorCase(cn, x, r(e))
        case TupCase(xs, e) => TupCase(xs, r(e))
      }
    }

    def r(e: Exp): Exp = {
      e match {
        case VariableExp(_) | StringExp(_) | BooleanExp(_) | IntExp(_) | UnitExp => e
        case BinopExp(e1, op, e2) => BinopExp(r(e1), op, r(e2))
        case FunctionExp(x, e) => FunctionExp(x, r(e))
        case AnonCallExp(VariableExp(Variable(name)), e) if functionNames.contains(name) => {
          NamedCallExp(FunctionName(name), r(e))
        }
        case AnonCallExp(e1, e2) => AnonCallExp(r(e1), r(e2))
        case NamedCallExp(fn, e) => NamedCallExp(fn, r(e))
        case IfExp(e1, e2, e3) => IfExp(r(e1), r(e2), r(e3))
        case BlockExp(vals, e) => BlockExp(functionCallPass(functionNames, vals), r(e))
        case TupleExp(es) => TupleExp(es.map(r))
        case AccessExp(e, n) => AccessExp(r(e), n)
        case ConstructorExp(cn, e) => ConstructorExp(cn, r(e))
        case MatchExp(e, cases) => MatchExp(r(e), cases.map(recCase))
      }
    }

    r(e)
  } // functionCallPass

  def parseWith[A](input: String, parser: => P[A]): Either[String, A] = {
    val tokens = new lexical.Scanner(input)
    phrase(parser)(tokens) match {
      case e: NoSuccess => Left(e.toString)
      case Success(res, _) => Right(res)
    }
  }

  def parseReplLine(input: String, defs: Map[FunctionName, Def]): Either[String, (ReplLine, Map[FunctionName, Def])] = {
    def translateExp(e: Exp): Exp = {
      functionCallPass(defs.keySet.map(_.name), e)
    }

    parseWith(input, replLine).right.map(rl => {
      rl match {
        case ReplDef(d) => {
          val newDefsList = functionCallPass((defs + (d.fn -> d)).values.toList)._2
          val newDefs = newDefsList.map(d => (d.fn -> d)).toMap
          (ReplDef(newDefs(d.fn)), newDefs)
        }
        case ReplVal(Val(x, e)) => {
          (ReplVal(Val(x, translateExp(e))), defs)
        }
        case ReplExp(e) => {
          (ReplExp(translateExp(e)), defs)
        }
        case l@ReplLoad(_) => {
          // shouldn't be possible, but can still be handled
          (l, defs)
        }
      }
    })
  }

  def parseFullTest(testName: String, input: String): Either[String, FullTest] = {
    parseWith(input, test).right.map(f => f(testName))
  }

  def parseProgram(input: String): Either[String, Program] = {
    parseWith(input, program)
  }

  // new ones will overwrite existing
  def parseDefsOnlyExistingDefs(input: String, existing: Map[FunctionName, Def]): Either[String, ParseWithExistingResult] = {
    def toPair(d: Def): (FunctionName, Def) = (d.fn -> d)

    parseDefsOnlyNoTranslation(input).right.map(newDefs => {
      val (toTranslate, repeats) =
        newDefs.foldLeft((existing, Set[FunctionName]()))((res, cur) => {
          val (curToTranslate, curRepeats) = res
          val nextRepeats = if (curToTranslate.contains(cur.fn)) curRepeats + cur.fn else curRepeats
          val nextToTranslate = curToTranslate + toPair(cur)
          (nextToTranslate, nextRepeats)
        })
      ParseWithExistingResult(functionCallPass(toTranslate.values.toList)._2.map(toPair).toMap,
                              repeats)
    })
  }

  // will do translation
  def parseDefsOnly(input: String): Either[String, List[Def]] = {
    parseDefsOnlyNoTranslation(input).right.map(defs => functionCallPass(defs)._2)
  }

  def parseDefsOnlyNoTranslation(input: String): Either[String, List[Def]] = {
    parseWith(input, defs)
  }

  def parseExpValue(functionNames: Set[String], input: String): Either[String, (Exp, Option[TestValue])] = {
    parseWith(input, expValue).right.map(
      { case (exp, opV) => (functionCallPass(functionNames, exp), opV) })
  }
  // BEGIN CODE FOR PARSING TEST VALUES

  // this code must be part of the same parser, as this
  // depends on program parsing.  With Scala's parser
  // combinators, we cannot easily combine parsers for
  // whole different languages (it rightfully
  // won't typecheck without doing a whole lot of extra work)

  lazy val testString: P[TestString] =
    stringLit ^^ TestString.apply

  lazy val testBoolean: P[TestBoolean] =
    boolean ^^ TestBoolean.apply

  lazy val testInt: P[TestInt] =
    numericLit ^^ (i => TestInt(i.toInt))

  lazy val testUnit: P[TestUnit.type] =
    "unit" ^^^ TestUnit

  lazy val testConstructor: P[TestConstructor] =
    constructorLike(testValue, TestConstructor.apply)

  lazy val testTuple: P[TestTuple] =
    tupleLike(testValue, TestTuple.apply)

  lazy val testValue: P[TestValue] =
    testString |
    testBoolean |
    testInt |
    testUnit |
    testConstructor |
    testTuple

  lazy val opTestValue: P[Option[TestValue]] =
    ("STUCK" ^^^ (None: Option[TestValue])) |
    (testValue ^^ Some.apply)

  lazy val test: P[String => FullTest] =
    program ~ (";;;" ~> opTestValue) ^^
    { case p ~ opV => (name: String) => FullTest(name, p, opV) }

  lazy val expValue: P[(Exp, Option[TestValue])] =
    exp ~ (";;;" ~> opTestValue) ^^
    { case e ~ opV => (e, opV) }

  lazy val replLine: P[ReplLine] =
    (defdef ^^ ReplDef.apply) |
    (valval ^^ ReplVal.apply) |
    (exp ^^ ReplExp.apply)

  def stripComment(line: String): String = {
    val index = line.indexOf("//")
    if (index != -1) {
      line.substring(0, index)
    } else {
      line
    }
  }

  def fileContents(filename: String): String = {
    scala.io.Source.fromFile(filename).getLines.map(stripComment).mkString("\n")
  } // fileContents
}
