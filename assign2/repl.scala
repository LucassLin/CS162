package simplescala.interpreter

import Aliases.Defs

sealed trait ReplLine
case class ReplDef(theDef: Def) extends ReplLine
case class ReplVal(theVal: Val) extends ReplLine
case class ReplExp(e: Exp) extends ReplLine
case class ReplLoad(path: String) extends ReplLine

class Repl {
  // begin instance variables
  private var defs: Map[FunctionName, Def] = Map()
  private var vals: Map[Variable, Value] = Map()
  private var tempNum: Int = 0
  // end instance variables

  def runExpressionToOpValue(e: Exp): Either[StuckException, Value] = {
    val interpreter = Interpreter(Program(defs.values.toSeq, e))
    val beforeVals = interpreter.initialState(e)
    val afterVals = beforeVals.copy(env = beforeVals.env ++ vals)
    Interpreter.catchStuckException(afterVals.runToValue)
  }

  def withExpressionValue(e: Exp, f: Value => Unit) {
    runExpressionToOpValue(e) match {
      case Left(e) => {
        println("GOT STUCK")
        e.printStackTrace()
      }
      case Right(v) => {
        f(v)
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

  def parseLine(line: String): Either[String, (ReplLine, Map[FunctionName, Def])] = {
    import Repl.LoadRegex
    // :load is handled internally as it is easier to treat
    // it in a line-based as opposed to a token-based setting
    line match {
      case LoadRegex(path) => Right((ReplLoad(path.trim), defs))
      case _ => SimpleScalaParser.parseReplLine(line, defs)
    }
  }


  def loadDefsFromFile(path: String) {
    import java.io.IOException
    try {
      Repl.handleParseError(
        SimpleScalaParser.parseDefsOnlyExistingDefs(
          SimpleScalaParser.fileContents(path),
          defs))(
          { case ParseWithExistingResult(newDefs, overwritten) => {
              defs = newDefs
              overwritten.foreach(fn => Repl.warnDefRedefined(fn.name))
          }
         })
    } catch {
      case e: IOException => {
        println(e.getMessage)
      }
    }
  }
          
  // line can be either a def, a val, or an expression
  def parseAndExecuteLine(line: String) {
    Repl.handleParseError(parseLine(line))(pair => {
      val (parsed, newDefs) = pair
      defs = newDefs
      parsed match {
        case ReplLoad(path) => {
          loadDefsFromFile(path)
        }
        case ReplDef(d) => {
          if (defs.contains(d.fn)) {
            Repl.warnDefRedefined(d.fn.name)
          }
        }
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
      }
    })
  } // parseLine

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
  val LoadRegex = """^\s*:load\s+(.*)$""".r

  def warnDefRedefined(name: String) {
    println("WARNING: Redefining def " + name)
  }

  def handleParseError[A](e: Either[String, A])(f: A => Unit) {
    e match {
      case Left(error) => {
        println("PARSE ERROR: " + error)
      }
      case Right(a) => {
        f(a)
      }
    }
  }

  def main(args: Array[String]) {
    (new Repl).runRepl()
  }
}

