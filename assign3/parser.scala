package simplescala.simplytyped

import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StdTokenParsers

case class OnlyDefs(tdefs: List[UserDefinedTypeDef],
                    defs: List[Def])

case class ParseWithExistingInput(existingTypedefs: Map[UserDefinedTypeName, UserDefinedTypeDef],
                                  existingDefs: Map[FunctionName, Def]) {
  def asResult(): ParseWithExistingResult = {
    ParseWithExistingResult(existingTypedefs,
                            existingDefs,
                            Set(),
                            Set())
  }

  def asResultTDef(tdef: UserDefinedTypeDef): ParseWithExistingResult = {
    assert(SimpleScalaParser.duplicateConstructors(existingTypedefs.values.toSeq, Seq(tdef)).isEmpty)
    ParseWithExistingResult(existingTypedefs + (tdef.un -> tdef),
                            existingDefs,
                            if (existingTypedefs.contains(tdef.un)) Set(tdef.un) else Set(),
                            Set())
  }

  def asResultDef(thedef: Def): ParseWithExistingResult = {
    ParseWithExistingResult(existingTypedefs,
                            existingDefs + (thedef.fn -> thedef),
                            Set(),
                            if (existingDefs.contains(thedef.fn)) Set(thedef.fn) else Set())
  }
}

case class ParseWithExistingResult(newTypedefs: Map[UserDefinedTypeName, UserDefinedTypeDef],
                                   newDefs: Map[FunctionName, Def],
                                   overwrittenTypedefs: Set[UserDefinedTypeName],
                                   overwrittenDefs: Set[FunctionName])

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
                             "=", "<", "<=", "._", ";;;", ":",
                             "|")
  lexical.reserved ++= Seq("unit", "if", "else", "match", "case", "val", "def",
                           "true", "false", "STUCK", "String", "Boolean",
                           "Int", "Unit", "algebraic", "ILLTYPED")

  val baseTypes: Map[String, Type] = {
    Map("String" -> StringType,
        "Boolean" -> BooleanType,
        "Int" -> IntegerType,
        "Unit" -> UnitType)
  }

  val LoadRegex = """^\s*:load\s+(.*)$""".r

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
    "-" ~> numericLit ^^ (i => -i.toInt) |
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

  lazy val userDefinedTypeName: P[UserDefinedTypeName] =
    upperCaseIdent ^^ UserDefinedTypeName.apply

  lazy val functionType: P[FunctionType] = {
    typetype ~ ("=>" ~> typetype) ^^ { case t1 ~ t2 => FunctionType(t1, t2) }
  }

  lazy val tupleType: P[TupleType] = {
    tupleLike(typetype, TupleType.apply)
  }

  lazy val userType: P[UserType] = {
    userDefinedTypeName ^^ UserType.apply
  }

  lazy val typetype: P[Type] = {
    functionType |
    tupleType |
    userType |
    baseTypes.map( { case (k, v) => k ^^^ v } ).reduceLeft(_ | _) |
    ("(" ~> typetype <~ ")")
  }

  lazy val primExp: P[Exp] =
    (matchExp |
     functionExp |
     anonCallExp | // named calls handled in second pass
     ifExp |
     blockExp |
     accessExp |
     tupleExp |
     constructorExp |
     "unit" ^^^ UnitExp |
     string ^^ StringExp.apply |
     boolean ^^ BooleanExp.apply |
     integer ^^ IntExp.apply |
     variable ^^ VariableExp.apply |
     ("(" ~> exp <~ ")"))

  lazy val multDivExp: P[Exp] = {
    binopExp(primExp, Map("*" -> BinopTimes,
                          "/" -> BinopDiv))
  }

  lazy val plusMinusExp: P[Exp] = {
    binopExp(multDivExp, Map("+" -> BinopPlus,
                             "-" -> BinopMinus))
  }

  lazy val lessLessThanExp: P[Exp] = {
    binopExp(plusMinusExp, Map("<=" -> BinopLTE,
                               "<" -> BinopLT))
  }

  lazy val andExp: P[Exp] = {
    binopExp(lessLessThanExp, Map("&&" -> BinopAnd))
  }

  lazy val orExp: P[Exp] = {
    binopExp(andExp, Map("||" -> BinopOr))
  }

  def binopExp(base: => P[Exp], ops: Map[String, Binop]): P[Exp] = {
    binop(base, ops.mapValues(bop => (x: Exp, y: Exp) => BinopExp(x, bop, y)))
  }

  def binop[A](base: => P[A], ops: Map[String, (A, A) => A]): P[A] = {
    val opsF = ops.toSeq.map( { case (stringOp, f) => stringOp ^^^ f } ).reduceLeft(_ | _)
    chainl1(base, opsF)
  }

  lazy val functionExp: P[FunctionExp] =
    "(" ~ variable ~ ":" ~ typetype ~ ")" ~ "=>" ~ exp ^^
    { case _ ~ x ~ _ ~ t ~ _ ~ _ ~ e => FunctionExp(x, t, e) }
    
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

  lazy val constructorDefinition: P[ConstructorDefinition] =
    constructorName ~ "(" ~ typetype ~ ")" ^^
    { case cn ~ _ ~ t ~ _ => ConstructorDefinition(cn, t) }

  lazy val userDefinedTypeDef: P[UserDefinedTypeDef] =
    ("algebraic" ~ userDefinedTypeName ~ "=" ~ rep1sep(constructorDefinition, "|")).flatMap(
      { case _ ~ un ~ _ ~ cdefs => {
          val consDups = duplicates(cdefs.map(_.cn.name))
          if (consDups.isEmpty) {
            success(UserDefinedTypeDef(un, cdefs))
          } else {
            failure("duplicate constructor names: " + consDups.mkString(", "))
          }
      } })

  lazy val defdef: P[Def] =
    "def" ~ notUpperCaseIdent ~ "(" ~ variable ~ ":" ~ typetype ~ ")" ~ ":" ~ typetype ~ "=" ~ exp ^^
    { case _ ~ fn ~ _ ~ x ~ _ ~ t1 ~ _ ~ _ ~ t2 ~ _ ~ e => Def(FunctionName(fn), x, t1, t2, e) }

  def duplicates[A](as: Seq[A]): Seq[A] =
    as.groupBy(n => n).values.filter(_.tail.nonEmpty).map(_.head).toSeq

  lazy val defs: P[List[Def]] = {
    rep(defdef).flatMap(defs => {
      val dups = duplicates(defs.toSeq.map(_.fn.name))
      if (dups.isEmpty) {
        success(defs)
      } else {
        failure("duplicate function names: " + dups.mkString(", "))
      }
    })
  }

  lazy val tdefs: P[List[UserDefinedTypeDef]] = {
    rep(userDefinedTypeDef).flatMap(tdefs => {
      val dupTypes = duplicates(tdefs.map(_.un.name))
      if (dupTypes.isEmpty) {
        val dupCons = duplicates(tdefs.flatMap(_.cdefs.map(_.cn.name)))
        if (dupCons.isEmpty) {
          success(tdefs)
        } else {
          failure("duplicate constructor names: " + dupCons.mkString(", "))
        }
      } else {
        failure("duplicate user-defined type names: " + dupTypes.mkString(", "))
      }
    })
  }

  lazy val program: P[Program] =
    tdefs ~ defs ~ exp ^^
    { case tdefs ~ fdefs ~ e => functionCallPass(tdefs, fdefs, e) }

  lazy val onlyDefs: P[OnlyDefs] =
    tdefs ~ defs ^^
    { case t ~ d => OnlyDefs(t, d) }

  def functionCallPass(defs: List[Def]): (Set[String], List[Def]) = {
    val functionNames = defs.map(_.fn.name).toSet
    (functionNames, defs.map(d => functionCallPass(functionNames, d)))
  }

  def functionCallPass(tdefs: List[UserDefinedTypeDef], defs: List[Def], e: Exp): Program = {
    val (functionNames, newDefs) = functionCallPass(defs)
    Program(tdefs,
            newDefs,
            functionCallPass(functionNames, e))
  }

  def functionCallPass(functionNames: Set[String], defdef: Def): Def = {
    defdef.copy(e = functionCallPass(functionNames, defdef.e))
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
        case FunctionExp(x, t, e) => FunctionExp(x, t, r(e))
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

  def parseReplLine(input: String, existing: ParseWithExistingInput): Either[String, (ReplLine, ParseWithExistingResult)] = {
    def translateExp(e: Exp): Exp = {
      functionCallPass(existing.existingDefs.keySet.map(_.name), e)
    }

    input match {
      case LoadRegex(path) => Right((ReplLoad(path), existing.asResult))
      case _ => {
        parseWith(input, replLine).right.flatMap(rl => {
          rl match {
            case ReplTDef(tdef) => {
              val dups = duplicateConstructors(existing.existingTypedefs.values.toSeq,
                                               Seq(tdef))
              if (dups.nonEmpty) {
                Left("Attempt to add algebraic with duplicate constructors: " +
                     dups.map(_.name).mkString(", "))
              } else {
                Right((rl, existing.asResultTDef(tdef)))
              }
            }
            case ReplDef(d) => {
              val newDefsList =
                functionCallPass((existing.existingDefs + (d.fn -> d)).values.toList)._2
              val newDefs = newDefsList.map(d => (d.fn -> d)).toMap
              Right(
                (ReplDef(newDefs(d.fn)),
                 ParseWithExistingResult(existing.existingTypedefs,
                                         newDefs,
                                         Set(),
                                         if (existing.existingDefs.contains(d.fn)) Set(d.fn) else Set())))
              }
            case ReplVal(Val(x, e)) => {
              Right((ReplVal(Val(x, translateExp(e))), existing.asResult))
            }
            case ReplExp(e) => {
              Right((ReplExp(translateExp(e)), existing.asResult))
            }
            case l@ReplLoad(_) => {
              // shouldn't be possible, but can still be handled
              Right((l, existing.asResult))
            }
          }
        })
      }
    }
  } // parseReplLine

  def parseFullTest(testName: String, input: String): Either[String, FullTest] = {
    parseWith(input, test).right.map(f => f(testName))
  }

  def parseProgram(input: String): Either[String, Program] = {
    parseWith(input, program)
  }

  def duplicateConstructors(existingTDefs: Seq[UserDefinedTypeDef],
                            newTDefs: Seq[UserDefinedTypeDef]): Set[ConstructorName] = {
    def asMap(input: Seq[UserDefinedTypeDef]): Map[UserDefinedTypeName, UserDefinedTypeDef] = {
      input.map(td => (td.un -> td)).toMap
    }

    def constructors(tdefs: Map[UserDefinedTypeName, UserDefinedTypeDef]): Set[ConstructorName] = {
      assert(tdefs.toSet.size == tdefs.size)
      tdefs.values.toSet.flatMap((td: UserDefinedTypeDef) => td.cdefs.map(_.cn).toSet)
    }

    val existingMap = asMap(existingTDefs)
    val newMap = asMap(newTDefs)
    val withoutRedefined = existingMap -- newMap.keys
    constructors(withoutRedefined).intersect(constructors(newMap))
  }

  // new ones will overwrite existing
  def parseDefsOnlyExistingDefs(input: String, existing: ParseWithExistingInput): Either[String, ParseWithExistingResult] = {
    def redefinedConstructors(newTDefs: List[UserDefinedTypeDef]): Set[ConstructorName] = {
      duplicateConstructors(existing.existingTypedefs.values.toSeq,
                            newTDefs.toSeq)
    }

    def asMap(defs: Seq[Def]): Map[FunctionName, Def] = {
      defs.map(d => (d.fn -> d)).toMap
    }

    def names(defs: Seq[Def]): Set[FunctionName] = {
      asMap(defs).keySet
    }

    parseDefsOnlyNoTranslation(input).right.flatMap(
      { case OnlyDefs(newTDefs, newDefs) => {
          val dups = redefinedConstructors(newTDefs)
          if (dups.nonEmpty) {
            Left("Duplicate constructors: " + dups.map(_.name).mkString(", "))
          } else {
            val defsMap = existing.existingDefs ++ asMap(newDefs)
            Right(
              ParseWithExistingResult(
                existing.existingTypedefs ++ newTDefs.map(td => (td.un -> td)),
                asMap(functionCallPass(defsMap.values.toList)._2),
                existing.existingTypedefs.keySet.intersect(newTDefs.map(_.un).toSet),
                existing.existingDefs.keySet.intersect(names(newDefs))))
          }
      }
     })
  }  // parseDefsOnlyExistingDefs

  // will do translation
  def parseDefsOnly(input: String): Either[String, OnlyDefs] = {
    parseDefsOnlyNoTranslation(input).right.map(
      { case OnlyDefs(tdefs, defs) => OnlyDefs(tdefs, functionCallPass(defs)._2) })
  }

  def parseDefsOnlyNoTranslation(input: String): Either[String, OnlyDefs] = {
    parseWith(input, onlyDefs)
  }

  def parseExpTestExpect(functionNames: Set[String], input: String): Either[String, (Exp, TestExpect)] = {
    parseWith(input, expTestExpect).right.map(
      { case (exp, te) => (functionCallPass(functionNames, exp), te) })
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
    integer ^^ TestInt.apply

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

  lazy val expectIllTyped: P[ExpectIllTyped.type] =
    "ILLTYPED" ^^^ ExpectIllTyped

  lazy val expectWellTypedStuck: P[ExpectWellTypedStuck] =
    "STUCK" ~ ";;;" ~ typetype ^^
    { case _ ~ _ ~ t => ExpectWellTypedStuck(t) }

  lazy val expectWellTypedValue: P[ExpectWellTypedValue] =
    testValue ~ (";;;" ~> typetype) ^^
    { case tv ~ t => ExpectWellTypedValue(tv, t) }

  lazy val testExpect: P[TestExpect] = 
    expectIllTyped |
    expectWellTypedStuck |
    expectWellTypedValue

  lazy val test: P[String => FullTest] =
    program ~ (";;;" ~> testExpect) ^^
    { case p ~ te => (name: String) => FullTest(name, p, te) }

  lazy val expTestExpect: P[(Exp, TestExpect)] =
    exp ~ (";;;" ~> testExpect) ^^
    { case e ~ te => (e, te) }

  lazy val replLine: P[ReplLine] =
    (userDefinedTypeDef ^^ ReplTDef.apply) |
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
