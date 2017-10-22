package simplescala.polytyped

import simplescala.interpreter.{StuckException,
                                Value,
                                Interpreter}

import simplescala.interpreter.Aliases.Defs

sealed trait ReplLine
case class ReplTDef(tdef: UserDefinedTypeDef) extends ReplLine
case class ReplDef(theDef: Def) extends ReplLine
case class ReplVal(theVal: Val) extends ReplLine
case class ReplExp(e: Exp) extends ReplLine
case class ReplLoad(path: String) extends ReplLine

class Repl {
  // begin instance variables
  private var tdefs: Map[UserDefinedTypeName, UserDefinedTypeDef] = Map()
  private var defs: Map[FunctionName, Def] = Map()
  private var vals: Map[Variable, Value] = Map()
  private var tempNum: Int = 0
  // end instance variables

  def existingInput(): ParseWithExistingInput = {
    ParseWithExistingInput(tdefs, defs)
  }

  def runExpressionToOpValue(e: Exp): Either[StuckException, Value] = {
    val interpreter = Interpreter(Program(tdefs.values.toSeq, defs.values.toSeq, e))
    val beforeVals = interpreter.initialState(e)
    val afterVals = beforeVals.copy(env = beforeVals.env ++ vals)
    Interpreter.catchStuckException(afterVals.runToValue)
  }

  def withExpressionValue(e: Exp, f: Value => Unit) {
    typeof(e) match {
      case Right(_) => {
        runExpressionToOpValue(e) match {
          case Left(e) => {
            println("GOT STUCK")
            Repl.ifDebug(e.printStackTrace())
          }
          case Right(v) => {
            f(v)
          }
        }
      }
      case Left(e)=> {
        println("ILL-TYPED")
        Repl.ifDebug(e.printStackTrace())
      }
    }
  }

  def freshTempVariable(): Variable = {
    val retval = Variable("res" + tempNum.toString)
    tempNum += 1
    retval
  }

  def addVarBinding(x: Variable, v: Value) {
    vals += (x -> v)
    println(x.name + " = " + TestValue.prettyString(v))
  }

  def typeof(e: Exp): Either[IllTyped, Type] = {
    Typechecker.eitherType(Program(tdefs.values.toSeq,
                                   defs.values.toSeq,
                                   e))
  }

  // returns true if there were no issues, else false
  def handleExistingResult(res: ParseWithExistingResult): Boolean = {
    val prog = Program(res.newTypedefs.values.toSeq,
                       res.newDefs.values.toSeq,
                       UnitExp)
    Typechecker.eitherType(prog) match {
      case Right(UnitType) => {
        tdefs = res.newTypedefs
        defs = res.newDefs
        res.overwrittenTypedefs.foreach(Repl.warnTDefRedefined)
        res.overwrittenDefs.foreach(Repl.warnDefRedefined)
        true
      }
      case Right(_) => {
        println("Typechecker cannot typecheck unit properly; not accepting defs")
        false
      }
      case Left(e) => {
        println("Type error in defs; not accepting defs")
        Repl.ifDebug(e.printStackTrace())
        false
      }
    }
  }

  def loadDefsFromFile(path: String) {
    import java.io.IOException
    try {
      Repl.handleParseError(
        SimpleScalaParser.parseOnlyDefsExistingDefs(
          SimpleScalaParser.fileContents(path),
          existingInput),
        handleExistingResult _)
    } catch {
      case e: IOException => {
        println(e.getMessage)
      }
    }
  }

  // line can be either a def, a val, or an expression
  def parseAndExecuteLine(line: String) {
    Repl.handleParseError(
      SimpleScalaParser.parseReplLine(line, existingInput),
      (pair: (ReplLine, ParseWithExistingResult)) => {
        val (parsed, res) = pair
        if (handleExistingResult(res)) {
          parsed match {
            case ReplTDef(_) | ReplDef(_) => ()
            case ReplVal(Val(x, e)) => {
                withExpressionValue(e, v => {
                  addVarBinding(x, v)
                })
            }
            case ReplExp(e) => {
              withExpressionValue(e, v => {
                addVarBinding(freshTempVariable(), v)
              })
            }
            case ReplLoad(path) => {
              loadDefsFromFile(path)
            }
          }
        }
      })
  } // parseAndExecuteLine

  def runRepl() {
    print("simplescala> ")
    var line = Console.readLine()
    while (line ne null) {
      parseAndExecuteLine(line)
      print("\nsimplescala> ")
      line = Console.readLine()
    }
  } // runRepl
}

object Repl {
  val DEBUG_MODE = false

  def warnTDefRedefined(un: UserDefinedTypeName) {
    println("WARNING: Redefining algebraic " + un.name)
  }

  def warnDefRedefined(fn: FunctionName) {
    println("WARNING: Redefining def " + fn.name)
  }

  def handleParseError[A](e: Either[String, A], f: A => Unit) {
    e match {
      case Left(error) => {
        println("PARSE ERROR: " + error)
      }
      case Right(a) => {
        f(a)
      }
    }
  }

  def ifDebug(what: => Unit) {
    if (DEBUG_MODE) {
      what
    }
  }

  def main(args: Array[String]) {
    (new Repl).runRepl()
  }
}

