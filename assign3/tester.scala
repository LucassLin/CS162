package simplescala.simplytyped

import simplescala.interpreter.Interpreter

import java.io.{File, FilenameFilter}

object FullTest {
  def prettyType(t: Type): String = {
    t match {
      case StringType => "String"
      case BooleanType => "Boolean"
      case IntegerType => "Integer"
      case UnitType => "Unit"
      case FunctionType(t1, t2) => prettyType(t1) + " => " + prettyType(t2)
      case TupleType(ts) => ts.map(prettyType).mkString("(", ", ", ")")
      case UserType(UserDefinedTypeName(name)) => name
    }
  } // prettyType
} // FullTest

sealed trait RunResult
case object Failure extends RunResult
case object SuccessNoException extends RunResult
case class SuccessException(e: IllTyped) extends RunResult

case class FullTest(testName: String, p: Program, res: TestExpect) {
  def run(): RunResult = {
    var retval: RunResult = Failure

    def passed(ill: Option[IllTyped]) {
      retval = ill.map(SuccessException.apply).getOrElse(SuccessNoException)
      println("passed")
    }

    def failed(error: String) {
      retval = Failure
      println("FAILED:\n" + error)
    }

    def runOnInterpreterWithTypeTest(gotType: Type, expectType: Type, opV: Option[TestValue]) {
      if (gotType == expectType) {
        runOnInterpreter(opV)
      } else {
        failed("Typechecker returned type " + FullTest.prettyType(gotType) +
               ", but was expected to get type " + FullTest.prettyType(expectType))
      }
    } // runOnInterpreterWithTypeTest

    def runOnInterpreter(opV: Option[TestValue]) {
      (Interpreter.runProgramToOpValue(p), opV) match {
        case (Left(_), None) => passed(None)
        case (Right(v), Some(tv)) => {
          tv.compareString(v) match {
            case Some(error) => failed(error)
            case None => passed(None)
          }
        }
        case (Left(e), Some(_)) => {
          failed("Got stuck, but wasn't expected to get stuck.  Exception follows:")
          e.printStackTrace()
        }
        case (Right(v), None) => {
          failed("Was expected to get stuck, but instead got value: " +
                 TestValue.prettyString(v))
        }
      }
    } // runOnInterpreter

    print("Running " + testName + ": ")
    try {
      (Typechecker.eitherType(p), res) match {
        case (Left(e), ExpectIllTyped) => passed(Some(e))
        case (Left(e), ExpectWellTypedStuck(_) | ExpectWellTypedValue(_, _)) => {
          failed("Typechecker returned ill-typed, but wasn't expected to " +
                 "return ill-typed.  Exception follows:")
          e.printStackTrace()
        }
        case (Right(gotType), ExpectIllTyped) => {
          failed("Typechecker returned type " + FullTest.prettyType(gotType) +
                 ", but was expected to be ill-typed")
        }
        case (Right(gotType), ExpectWellTypedStuck(expectType)) => {
          runOnInterpreterWithTypeTest(gotType, expectType, None)
        }
        case (Right(gotType), ExpectWellTypedValue(expectValue, expectType)) => {
          runOnInterpreterWithTypeTest(gotType, expectType, Some(expectValue))
        }
      }
    } catch {
      case e: Throwable => {
        failed("crash occurred.  Exception follows:")
        e.printStackTrace()
      }
    }
    retval
  } // run
} // FullTest

object SimpleScalaFilenameFilter extends FilenameFilter {
  def accept(file: File, name: String): Boolean = {
    name.endsWith(".simplescala")
  } // accept
} // SimpleScalaFilenameFilter

object FullTestSuite {
  type ExceptionSignature = Int

  def foreachFile(dirname: String, f: File => Unit) {
    Option(new File(dirname).listFiles(SimpleScalaFilenameFilter)).map(_.foreach(f))
  } // foreachFile

  // filename, contents pairs
  def foreachFileContents(dirname: String, f: (String, String) => Unit) {
    foreachFile(dirname,
                file =>
                  f(file.getName,
                    SimpleScalaParser.fileContents(file.getPath)))
  } // foreachFileContents

  def isDir(dirname: String): Boolean = {
    new File(dirname).isDirectory
  }

  def withDirectory(dirname: String)(f: => Unit) {
    if (isDir(dirname)) {
      f
    } else {
      println("Not a directory: " + dirname)
    }
  }

  def signature(e: IllTyped): Option[ExceptionSignature] = {
    if (e.inTypeOf) {
      e.getStackTrace.headOption.map(_.getLineNumber)
    } else {
      None
    }
  }
} // FullTestSuite

class FullTestSuite {
  import FullTestSuite.{foreachFileContents,
                        withDirectory,
                        signature,
                        ExceptionSignature}

  // begin instance variables
  private var numPassed = 0
  private var numFailed = 0
  private var uniqueSignatures: Set[ExceptionSignature] = Set()
  // end instance variables

  def runFullTest(filename: String, t: Either[String, FullTest]) {
    t match {
      case Left(error) => {
        println("COULD NOT PARSE " + filename + "\n" + error)
      }
      case Right(test) => {
        test.run() match {
          case Failure => {
            numFailed += 1
          }
          case SuccessNoException => {
            numPassed += 1
          }
          case SuccessException(e) => {
            signature(e).map(es => {
              uniqueSignatures += es
            })
            numPassed += 1
          }
        }
      }
    }
  } // runFullTest

  def runSingleTestSuite(dirname: String) {
    withDirectory(dirname) {
      foreachFileContents(dirname, (filename, contents) => {
        runFullTest(filename, SimpleScalaParser.parseFullTest(filename, contents))
      })
    }
  } // runSingleTestSuite

  def runMultiTestSuite(defsFile: String, dirname: String) {
    withDirectory(dirname) {
      SimpleScalaParser.parseDefsOnly(SimpleScalaParser.fileContents(defsFile)) match {
        case Left(error) => {
          println("FAILED TO PARSE DEFS FILE: " + defsFile + "\n" + error)
        }
        case Right(OnlyDefs(tdefs, defs)) => {
          val functionNames = defs.map(_.fn.name).toSet
          foreachFileContents(dirname, (filename, contents) => {
            runFullTest(
              filename,
              SimpleScalaParser.parseExpTestExpect(functionNames, contents).right.map(
                { case (exp, te) => FullTest(filename, Program(tdefs, defs, exp), te) }))
          })
        }
      }
    }
  } // runMultiTestSuite

  def numSignatures(): Int = {
    uniqueSignatures.size
  }

  def printResults() {
    println("NUM PASSED: " + numPassed)
    println("NUM FAILED: " + numFailed)
    println("PERCENTAGE: " + (numPassed.toDouble / (numPassed + numFailed) * 100))
    println("NUM UNIQUE ILL-TYPED IN TYPEOF: " + numSignatures)
  }
} // FullTestSuite

// expectation: each file is one program along with the expected value
object SingleTester {
  def usage() {
    println("Needs a directory holding test files")
  }

  def main(args: Array[String]) {
    if (args.length != 1) {
      usage()
    } else {
      val ts = new FullTestSuite()
      ts.runSingleTestSuite(args(0))
      ts.printResults()
    }
  }
} // SingleTester

// expectation: one list of defs with an arbitrary number of files
// each holding expression / value pairs
object MultiTester {
  def usage() {
    println("Takes the following parameters")
    println("-File holding a list of defs")
    println("-File holding an expression to evaluate, along with the value")
  }

  def main(args: Array[String]) {
    if (args.length != 2) {
      usage()
    } else {
      val ts = new FullTestSuite()
      ts.runMultiTestSuite(args(0), args(1))
      ts.printResults()
    }
  } // main  
} // MultiTester
