package simplescala.interpreter

import java.io.{File, FilenameFilter}

case class FullTest(testName: String, p: Program, opV: Option[TestValue]) {
  // returns true if passed, else false
  // doing this with mutable state is messy, but this avoids needing
  // to get the stack trace as a string
  def run(): Boolean = {
    var retval = true

    def passed() {
      retval = true
      println("passed")
    }

    def failed(error: String) {
      retval = false
      println("FAILED:\n" + error)
    }

    print("Running " + testName + ": ")
    try {
      (Interpreter.runProgramToOpValue(p), opV) match {
        case (Left(_), None) => passed()
        case (Right(v), Some(tv)) => {
          tv.compareString(v) match {
            case Some(error) => failed(error)
            case None => passed()
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
} // FullTestSuite

class FullTestSuite {
  import FullTestSuite.{foreachFileContents, withDirectory}

  // begin instance variables
  var numPassed = 0
  var numFailed = 0
  // end instance variables

  def runFullTest(filename: String, t: Either[String, FullTest]) {
    t match {
      case Left(error) => {
        println("COULD NOT PARSE " + filename + "\n" + error)
      }
      case Right(test) => {
        if (test.run()) {
          numPassed += 1
        } else {
          numFailed += 1
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
        case Right(defs) => {
          val functionNames = defs.map(_.fn.name).toSet
          foreachFileContents(dirname, (filename, contents) => {
            runFullTest(
              filename,
              SimpleScalaParser.parseExpValue(functionNames, contents).right.map(
                { case (exp, opV) => FullTest(filename, Program(defs, exp), opV) }))
          })
        }
      }
    }
  } // runMultiTestSuite

  def printResults() {
    println("NUM PASSED: " + numPassed)
    println("NUM FAILED: " + numFailed)
    println("PERCENTAGE: " + (numPassed.toDouble / (numPassed + numFailed) * 100))
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
