package simplescala.polytyped

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

// Named function calls now are distinguishable from anonymous
// function calls, as named function calls now take types.
// Even if no types are provided, the syntax requires `[]`.
// This means we don't need to do any translation anymore.
object SimpleScalaParser extends StdTokenParsers with PackratParsers {
  import scala.util.parsing.combinator.lexical.StdLexical

  type P[+T] = PackratParser[T]
  type Error = String
  type Tokens = StdLexical

  val lexical = new StdLexical
  lexical.delimiters ++= Seq("(", ")", "{", "}", ",", "=>",
                             "+", "-", "*", "/", "&&", "||",
                             "=", "<", "<=", "._", ";;;", ":",
                             "|", "[", "]")
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

  lazy val functionName: P[FunctionName] =
    notUpperCaseIdent ^^ FunctionName.apply

  lazy val constructorName: P[ConstructorName] =
    upperCaseIdent ^^ ConstructorName.apply

  lazy val userDefinedTypeName: P[UserDefinedTypeName] =
    upperCaseIdent ^^ UserDefinedTypeName.apply

  lazy val typeVariable: P[TypeVariable] =
    upperCaseIdent ^^ TypeVariable.apply

  lazy val functionType: P[FunctionType] = {
    typetype ~ ("=>" ~> typetype) ^^ { case t1 ~ t2 => FunctionType(t1, t2) }
  }

  lazy val tupleType: P[TupleType] = {
    tupleLike(typetype, TupleType.apply)
  }

  lazy val userType: P[UserType] = {
    userDefinedTypeName ~ typesList ^^
    { case un ~ types => UserType(un, types) }
  }

  lazy val typeVariableType: P[TypeVariableType] = {
    typeVariable ^^ TypeVariableType.apply
  }

  lazy val typetype: P[Type] = {
    functionType |
    tupleType |
    userType |
    typeVariableType |
    baseTypes.map( { case (k, v) => k ^^^ v } ).reduceLeft(_ | _) |
    ("(" ~> typetype <~ ")")
  }

  lazy val primExp: P[Exp] =
    (matchExp |
     functionExp |
     anonCallExp |
     namedCallExp |
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

  lazy val namedCallExp: P[NamedCallExp] =
    functionName ~ typesList ~ ("(" ~> exp <~ ")") ^^
    { case fn ~ types ~ e => NamedCallExp(fn, types, e) }

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

  lazy val typeVariableList: P[List[TypeVariable]] = {
    ("[" ~> repsep(typeVariable, ",") <~ "]").flatMap(typevars => {
      val dups = duplicates(typevars.map(_.name))
      if (dups.isEmpty) {
        success(typevars)
      } else {
        failure("duplicate type variables: " + dups.mkString(", "))
      }
    })
  }

  lazy val typesList: P[List[Type]] =
    "[" ~> repsep(typetype, ",") <~ "]"

  lazy val constructorExp: P[ConstructorExp] =
    constructorName ~ typesList ~ ("(" ~> exp <~ ")") ^^
    { case cn ~ types ~ e => ConstructorExp(cn, types, e) }

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
    constructorName ~ ("(" ~> typetype <~ ")") ^^
    { case cn ~ t => ConstructorDefinition(cn, t) }

  lazy val userDefinedTypeDef: P[UserDefinedTypeDef] =
    ("algebraic" ~ userDefinedTypeName ~ typeVariableList ~ "=" ~ rep1sep(constructorDefinition, "|")).flatMap(
      { case _ ~ un ~ typevars ~ _ ~ cdefs => {
          val consDups = duplicates(cdefs.map(_.cn.name))
          if (consDups.isEmpty) {
            success(UserDefinedTypeDef(un, typevars, cdefs))
          } else {
            failure("duplicate constructor names: " + consDups.mkString(", "))
          }
      } })

  lazy val defdef: P[Def] =
    "def" ~ functionName ~ typeVariableList ~ "(" ~ variable ~ ":" ~ typetype ~ ")" ~ ":" ~ typetype ~ "=" ~ exp ^^
    { case _ ~ fn ~ typevars ~ _ ~ x ~ _ ~ t1 ~ _ ~ _ ~ t2 ~ _ ~ e =>
        Def(fn, typevars, x, t1, t2, e) }

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
    { case tdefs ~ fdefs ~ e => Program(tdefs, fdefs, e) }

  lazy val onlyDefs: P[OnlyDefs] =
    tdefs ~ defs ^^
    { case t ~ d => OnlyDefs(t, d) }

  def parseWith[A](input: String, parser: => P[A]): Either[String, A] = {
    val tokens = new lexical.Scanner(input)
    phrase(parser)(tokens) match {
      case e: NoSuccess => Left(e.toString)
      case Success(res, _) => Right(res)
    }
  }

  def parseReplLine(input: String, existing: ParseWithExistingInput): Either[String, (ReplLine, ParseWithExistingResult)] = {
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
              Right((rl, existing.asResultDef(d)))
            }
            case o => {
              Right((o, existing.asResult))
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
  def parseOnlyDefsExistingDefs(input: String, existing: ParseWithExistingInput): Either[String, ParseWithExistingResult] = {
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

    parseOnlyDefs(input).right.flatMap(
      { case OnlyDefs(newTDefs, newDefs) => {
          val dups = redefinedConstructors(newTDefs)
          if (dups.nonEmpty) {
            Left("Duplicate constructors: " + dups.map(_.name).mkString(", "))
          } else {
            Right(
              ParseWithExistingResult(
                existing.existingTypedefs ++ newTDefs.map(td => (td.un -> td)),
                existing.existingDefs ++ asMap(newDefs),
                existing.existingTypedefs.keySet.intersect(newTDefs.map(_.un).toSet),
                existing.existingDefs.keySet.intersect(names(newDefs))))
          }
      }
     })
  }  // parseOnlyDefsExistingDefs

  def parseOnlyDefs(input: String): Either[String, OnlyDefs] = {
    parseWith(input, onlyDefs)
  }

  def parseExpTestExpect(functionNames: Set[String], input: String): Either[String, (Exp, TestExpect)] = {
    parseWith(input, expTestExpect)
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
    constructorName ~ ("(" ~> testValue <~ ")") ^^
    { case cn ~ tv => TestConstructor(cn, tv) }

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
