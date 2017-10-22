package miniprolog.tester

import miniprolog.interpreter._    

case class Test(rawQuery: String, rawExpected: Seq[Seq[(Symbol, Value)]]) {
  import miniprolog.syntax.lowlevel.Variable

  def printFail(msg: String) {
    println("FAIL: " + rawQuery + ": " + msg)
  }

  @scala.annotation.tailrec
  final def checkResult(expected: List[(Symbol, Value)],
                        resultNum: Int,
                        actual: Map[Variable, Value]): Boolean = {
    expected match {
      case Nil => true
      case (Symbol(varName), expectedValue) :: tail => {
        val variable = Variable(varName)
        actual.get(variable) match {
          case Some(actualValue) => {
            if (expectedValue != actualValue) {
              printFail("variable " + varName + 
                        " for solution " + resultNum +
                        ": expected " + Interpreter.buildPrint(expectedValue)
                        + " but received " + Interpreter.buildPrint(actualValue))
              false
            } else {
              checkResult(tail, resultNum, actual)
            }
          }
          case None => {
            printFail("variable " + varName + " misssing for solution " + resultNum)
            false
          }
        }
      }
    }
  }

  def runTest(session: DBSession): Boolean = {
    try {
      val results = session.queryResults(rawQuery)
      val resLen = results.length
      val expLen = rawExpected.length
      
      if (resLen != expLen) {
        printFail("Expected " + expLen + " results; received " + resLen)
        false
      } else {
        (rawExpected, 1.to(expLen), results).zipped.forall(
          { case (expected, num, actual) =>
            checkResult(expected.toList, num, actual) })
      }
    } catch {
      case _: Throwable => {
        printFail("crashed.")
        false
      }
    }
  }
} // Test

object Tests {
  val zero = IntValue(0)
  val one = IntValue(1)
  val two = IntValue(2)
  val three = IntValue(3)
  val four = IntValue(4)
  val five = IntValue(5)
  val six = IntValue(6)
  val seven = IntValue(7)
  val eight = IntValue(8)
  val nine = IntValue(9)
  val ten = IntValue(10)

  def asPrologList(lst: List[Value]): TermValue = {
    lst.foldRight(TermValue(Symbol("[]"), Seq()))((cur, res) =>
      TermValue(Symbol("."), Seq(cur, res)))
  }

  val baseUnify1 =
    Test("X = 1.",
         Seq(Seq('X -> one)))
  val baseUnify2 =
    Test("1 = X.",
         Seq(Seq('X -> one)))
  val baseUnify3 =
    Test("foo(X, Y) = foo(1, 2).",
         Seq(Seq('X -> one,
                 'Y -> two)))
  val baseUnify4 =
    Test("foo(1, 2) = foo(X, Y).",
         Seq(Seq('X -> one,
                 'Y -> two)))
  val baseUnify5 =
    Test("foo(1, Y) = foo(X, 2).",
         Seq(Seq('X -> one,
                 'Y -> two)))
  val baseUnify6 =
    Test("foo(X, 2) = foo(1, Y).",
         Seq(Seq('X -> one,
                 'Y -> two)))
  val baseUnify7 =
    Test("foo(X, X) = foo(1, 2).",
         Seq())
  val baseUnify8 =
    Test("foo(1, X, 2) = foo(X, 1, X).",
         Seq())
  val baseUnify9 =
    Test("foo(bar(X, Y), baz(A, B)) = foo(bar(1, 2), baz(3, 4)).",
         Seq(Seq('X -> one, 'Y -> two, 'A -> three, 'B -> four)))
  val baseUnify10 =
    Test("foo(bar(1, 2), baz(3, 4)) = foo(bar(X, Y), baz(A, B)).",
         Seq(Seq('X -> one, 'Y -> two, 'A -> three, 'B -> four)))
  val baseUnify11 =
    Test("foo(1, 2) = bar(1, 2).",
         Seq())
  val baseUnify12 =
    Test("foo(1, 2, 3) = foo(1, 2).",
         Seq())
  val baseUnify13 =
    Test("foo(bar, 1) = foo(1, bar).",
         Seq())
  val baseUnify14 =
    Test("X = Y, Y = Z, Z = A, A = B, B = 1.",
         Seq(Seq('X -> one, 'Y -> one, 'A -> one, 'B -> one)))
  val baseUnify15 =
    Test("X = B, Y = X, X = A, B = Y, X = 1.",
         Seq(Seq('X -> one, 'Y -> one, 'A -> one, 'B -> one)))

  val relLt =
    Test("1 < 2.",
         Seq(Seq()))
  val relGt =
    Test("2 > 1.",
         Seq(Seq()))
  val relEq1 =
    Test("1 =:= 1.",
         Seq(Seq()))
  val relEq2 =
    Test("1 =:= 2.",
         Seq())

  val is1 =
    Test("X is 1 + 1.",
         Seq(Seq('X -> two)))
  val is2 =
    Test("X is 1 - 1.",
         Seq(Seq('X -> zero)))
  val is3 =
    Test("X is 2 * 4.",
         Seq(Seq('X -> eight)))
  val is4 =
    Test("X is 4 / 2.",
         Seq(Seq('X -> two)))

  val unify1 =
    Test("unify(X, 1).",
         Seq(Seq('X -> one)))
  val unify2 =
    Test("unify(1, X).",
         Seq(Seq('X -> one)))

  val append1 =
    Test("myAppend([1,2], [3,4], X).",
         Seq(Seq('X -> asPrologList(List(one, two, three, four)))))

  val append2 =
    Test("myAppend(X, Y, [1,2,3,4]).",
         Seq(Seq('X -> asPrologList(List()),
                 'Y -> asPrologList(List(one, two, three, four))),
             Seq('X -> asPrologList(List(one)),
                 'Y -> asPrologList(List(two, three, four))),
             Seq('X -> asPrologList(List(one, two)),
                 'Y -> asPrologList(List(three, four))),
             Seq('X -> asPrologList(List(one, two, three)),
                 'Y -> asPrologList(List(four))),
             Seq('X -> asPrologList(List(one, two, three, four)),
                 'Y -> asPrologList(List()))))

  val append3 =
    Test("myAppend([1,2], [3,4], [1,2,3,4]).",
         Seq(Seq()))

  val length1 =
    Test("myLength([1,2,3], Len).",
         Seq(Seq('Len -> three)))
  val length2 =
    Test("myLength([1,2,3], 3).",
         Seq(Seq()))
  
  val function2_1 =
    Test("function2(A).",
         Seq(Seq('A -> one),
             Seq('A -> two)))
  val function2_2 =
    Test("function2(1).",
         Seq(Seq()))
  val function2_3 =
    Test("function2(2).",
         Seq(Seq()))
  val function2_4 =
    Test("function2(3).",
         Seq())

  val function_1 =
    Test("function(A).",
         Seq(Seq('A -> three),
             Seq('A -> four),
             Seq('A -> one),
             Seq('A -> two)))
  val function_2 =
    Test("function(3).",
         Seq(Seq()))
  val function_3 =
    Test("function(4).",
         Seq(Seq()))
  val function_4 =
    Test("function(1).",
         Seq(Seq()))
  val function_5 =
    Test("function(2).",
         Seq(Seq()))
  val function_6 =
    Test("function(6).",
         Seq())

  val function3_1 =
    Test("function3(A).",
         Seq(Seq('A -> five),
             Seq('A -> six)))
  val function3_2 =
    Test("function3(5).",
         Seq(Seq()))
  val function3_3 =
    Test("function3(6).",
         Seq(Seq()))
  val function3_4 =
    Test("function3(7).",
         Seq())

  val tests = Seq(baseUnify1, baseUnify2, baseUnify3, baseUnify4,
                  baseUnify5, baseUnify6, baseUnify7, baseUnify8,
                  baseUnify9, baseUnify10, baseUnify11, baseUnify12,
                  baseUnify13, baseUnify14, baseUnify15,
                  relLt, relGt, relEq1, relEq2,
                  is1, is2, is3, is4,
                  unify1, unify2,
                  append1, append2, append3,
                  length1, length2,
                  function2_1, function2_2, function2_3, function2_4,
                  function_1, function_2, function_3, function_4, function_5, function_6,
                  function3_1, function3_2, function3_3, function3_4)

  def main(args: Array[String]) {
    val session = new DBSession("tests.pl")
    val numPassed = tests.map(test => if (test.runTest(session)) 1 else 0).sum
    println("Passed: " + numPassed + "/" + tests.length)
  }
}

