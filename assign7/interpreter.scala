package miniprolog.interpreter

import miniprolog.syntax.lowlevel._
import miniprolog.syntax.lowlevel.Aliases.Name

sealed trait ReadLineResult
case object Stop extends ReadLineResult
case object Continue extends ReadLineResult

class DBSession(dbFile: String) {
  import miniprolog.parser._
  import miniprolog.translator._

  // begin constructor
  private val translator = new Translator
  val procedures =
    translator.translateClauses(
      Parser.getAst(scala.io.Source.fromFile(dbFile).mkString))
  val db =
    procedures.map(
      { case c@Clause(name, formalParams, _, _) =>
          ((name -> formalParams.length) -> c) } ).toMap
  // end constructor

  def runQuery(queryString: String,
               makeStateTrans: Seq[Variable] => (StateBehavior => Boolean)) {
    val (query, allOrderedVars) =
      translator.translateQuery(
        Parser.parseQuery(queryString))
    val interpreter = new Interpreter(db)
    interpreter.runQuery(query, makeStateTrans(allOrderedVars))
  }

  def queryResults(queryString: String): Seq[Map[Variable, Value]] = {
    val results = scala.collection.mutable.Buffer[Map[Variable, Value]]()

    def collectResult(behavior: StateBehavior): Boolean = {
      behavior match {
        case GettingCurrentSolution => true
        case HasMoreSolutions(solution) => {
          results += solution
          true
        }
        case HasSolutionNoMoreSolutions(solution) => {
          results += solution
          false
        }
        case NoSolutionNoMoreSolutions => false
      }
    }
      
    runQuery(queryString, _ => collectResult)
    results.toSeq
  }
} // DBSession

object Interpreter {
  type Nat = Int // hacky, but it is sufficient for our case
  type ClauseDB = Map[(Name, Nat), Clause]
  type Choice = (Body, Env, EquivClasses, List[Kont])
  type Env = Map[Variable, Placeholder]

  def printRet[A](a: A): A = {
    println(a)
    a
  }

  def fullLookup(v: Value, eq: EquivClasses): Value = {
    eq.lookup(v) match {
      case iv: IntValue => iv
      case pl: Placeholder => pl
      case TermValue(name, vs) => TermValue(name, vs.map(v => fullLookup(v, eq)))
    }
  }

  // assumes that fullLookup has already been called on the value
  def buildPrint(v: Value, inList: Boolean = false): String = {
    v match {
      case IntValue(n) => n.toString
      case Placeholder(n) => "_" + n.toString
      case TermValue(symbol, Nil) => {
        val symbolString = symbol.toString
        if (symbolString == "'[]") {
          if (inList) "]" else "[]"
        } else {
          symbolString
        }
      }
      case TermValue(symbol, head :: tail :: Nil) if symbol.toString == "'." => {
        val start = if (inList) ", " else "["
        start + buildPrint(head) + buildPrint(tail, true)
      }
      case TermValue(symbol, vals) => {
        symbol.toString + "(" + vals.map(v => buildPrint(v)).mkString(", ") + ")"
      }
    }
  } // buildPrint

  @scala.annotation.tailrec
  def readLineResult(): ReadLineResult = {
    Console.readLine().trim match {
      case "." => Stop
      case ";" => Continue
      case _ => {
        println("Please type '.' or ';'")
        readLineResult()
      }
    }
  }

  def isInteger(s: String): Boolean = {
    try {
      Integer.parseInt(s)
      true
    } catch {
      case _: NumberFormatException => false
    }
  }

  def makeInteractiveStateTrans(allOrderedVars: Seq[Variable]): StateBehavior => Boolean = {
    val varsToPrint = allOrderedVars.filterNot(x => isInteger(x.varName))
    def printVars(solution: Map[Variable, Value]) {
      if (varsToPrint.isEmpty) {
        println("true")
      } else {
        varsToPrint.foreach(x =>
          println(x.varName + " = " + buildPrint(solution(x))))
      }
    }

    (behavior: StateBehavior) => {
      behavior match {
        case GettingCurrentSolution => true
        case HasMoreSolutions(solution) => {
          printVars(solution)
          readLineResult() match {
            case Stop => false
            case Continue => true
          }
        }
        case HasSolutionNoMoreSolutions(solution) => {
          printVars(solution)
          false
        }
        case NoSolutionNoMoreSolutions => {
          println("false")
          false
        }
      }
    }
  } // makeInteractiveStateTrans

  def main(args: Array[String]) {
    if (args.length != 2) {
      println("Needs a file holding database clauses and a query.")
    } else {
      val session = new DBSession(args(0))
      session.runQuery(args(1), makeInteractiveStateTrans)
    }
  } // main
}
import Interpreter._

sealed trait Value
case class IntValue(i: Int) extends Value
case class TermValue(name: Name, values: Seq[Value]) extends Value
case class Placeholder(n: Nat) extends Value

sealed trait Kont
case class AndK(b: Body) extends Kont
case class RestoreK(env: Env) extends Kont

case class EquivClasses(map: Map[Placeholder, Value]) {
  // slight signature change: `map` above is now roughly `eq` in the math
  def lookup(v: Value): Value = {
    v match {
      case Placeholder(p) if (map.contains(Placeholder(p))) => lookup(map(Placeholder(p)))
      case _ => v
    }    
  }
  // slight signature change: `map` above is now roughly `eq` in the math
  def addRelation(p: Placeholder, v: Value): EquivClasses = {
    if (lookup(v) == p) EquivClasses(map) else EquivClasses(map+(p->lookup(v)))
}
}
class StuckException extends Exception

sealed trait StateBehavior
case object GettingCurrentSolution extends StateBehavior
case class HasMoreSolutions(curSolution: Map[Variable, Value]) extends StateBehavior
case class HasSolutionNoMoreSolutions(curSoluion: Map[Variable, Value]) extends StateBehavior
case object NoSolutionNoMoreSolutions extends StateBehavior

class Interpreter(val db: ClauseDB) {
  // begin instance variables
  private var placeholderCounter: Int = 0
  // end instance variables

  def freshPlaceholder(): Placeholder = {
    val retval = Placeholder(placeholderCounter)
    placeholderCounter += 1
    retval
  }

  def unifyVals(v1: Value, v2: Value, eq: EquivClasses): Option[EquivClasses] = {
    (eq.lookup(v1), eq.lookup(v2)) match {
      case (Placeholder(i), _) => Some(eq.addRelation(Placeholder(i), eq.lookup(v2)))
      case (IntValue(i), Placeholder(p)) => Some(eq.addRelation(Placeholder(p), eq.lookup(v1)))
      case (TermValue(name,s), Placeholder(p)) => Some(eq.addRelation(Placeholder(p), eq.lookup(v1)))
      case (IntValue(i), IntValue(ii)) if(i==ii) => Some(eq)
      case (TermValue(name,v5), TermValue(name1,v6)) if(name==name1 && v5.length==v6.length) => unifyMultiVals((v5 zip v6).toList, eq)
      case _ => None
    }
    
}

  def unifyMultiValsHelper(vs: List[(Value, Value)], opEq: Option[EquivClasses]): Option[EquivClasses] = {
    opEq match{
      case Some(eq) => unifyMultiVals(vs, eq)
      case _ => None
    }

  }

  def unifyMultiVals(vs: List[(Value, Value)], eq: EquivClasses): Option[EquivClasses] = {
      vs match{
      case (v1, v2)::vs1 => unifyMultiValsHelper(vs1, unifyVals(v1, v2, eq))
      case _ => Some(eq)
    }
  }

  def newScope(vars: Set[Variable]): Env = {
    vars.map(x => (x -> freshPlaceholder())).toMap
  }

  def callBodyEnvEq(actualParams: Seq[Variable],
                    clause: Clause,
                    oldEnv: Env,
                    eq: EquivClasses): (Body, Env, EquivClasses) = {
    val Clause(_, formalParams, localVars, body) = clause
    assert(actualParams.length == formalParams.length)
    val newEnv = newScope((formalParams ++ localVars).toSet)
    val newEq = callBodyEnvEqHelper(formalParams.toList,
                                    actualParams.toList,
                                    oldEnv, newEnv, eq)
    (body, newEnv, newEq)
  }

  @scala.annotation.tailrec
  final def callBodyEnvEqHelper(formalParams: List[Variable], actualParams: List[Variable],
                                oldEnv: Env, newEnv: Env, eq: EquivClasses): EquivClasses = {
    (formalParams, actualParams) match {
      case (formalParam :: restFormal, actualParam :: restActual) => {
        callBodyEnvEqHelper(restFormal,
                            restActual,
                            oldEnv, newEnv,
                            eq.addRelation(newEnv(formalParam), eq.lookup(oldEnv(actualParam))))
      }
      case (Nil, Nil) => eq
      case _ => throw new StuckException
    }
  }

  def relationalHolds(i1: Int, op: RelationalOp, i2: Int): Boolean = {
    op match {
      case LT => i1 < i2
      case LTE => i1 <= i2
      case GT => i1 > i2
      case GTE => i1 >= i2
      case EQ => i1 == i2
      case NEQ => i1 != i2
    }
  }

  def evalArithExp(e: ArithExp, env: Env, eq: EquivClasses): Int = {
    e match {
      case IntExp(i) => i
      case VarExp(x) => {
        eq.lookup(env(x)) match {
          case IntValue(i) => i
          case _ => throw new StuckException
        }
      }
      case BinExp(e1, op, e2) => {
        evalArithExpHelper(evalArithExp(e1, env, eq),
                           op,
                           evalArithExp(e2, env, eq))
      }
    }
  }

  def evalArithExpHelper(i1: Int, op: ArithOp, i2: Int): Int = {
    op match {
      case ArithPlus => i1 + i2
      case ArithMinus => i1 - i2
      case ArithTimes => i1 * i2
      case ArithDiv if i2 != 0 => i1 / i2
      case _ => throw new StuckException
    }
  }

  def evalCompoundTerm(t: CompoundTerm, env: Env, eq: EquivClasses): TermValue = {
    val CompoundTerm(name, xs) = t
    TermValue(name, xs.map(x => eq.lookup(env(x))))
  }

  case class State(b: Body, env: Env, eq: EquivClasses, ks: List[Kont], chs: List[Choice]) {
    def getBehavior(): StateBehavior = {
      lazy val solution = env.mapValues(pl => fullLookup(pl, eq))
      (b, ks, chs) match {
        case (True, Nil, _ :: _) => HasMoreSolutions(solution)
        case (True, Nil, Nil) => HasSolutionNoMoreSolutions(solution)
        case (Fail, _, Nil) => NoSolutionNoMoreSolutions
        case _ => GettingCurrentSolution
      }
    }

    def nextState(): State = {
      b match {
        case And(b1, b2) => State(b1, env, eq, AndK(b2)::ks, chs)
        case Choose(b1, b2) => State(b1, env, eq, ks, (b2,env,eq,ks)::chs)
        case Unify(x1,x2) => {
        if (unifyVals(env(x1),env(x2),eq).isEmpty) State(Fail,env,eq,ks,chs) else State(True,env,unifyVals(env(x1),env(x2),eq).get,ks,chs)
      }
      case Call(t) => {
        val x=callBodyEnvEq(t.variables,db((t.name,t.variables.length)),env,eq)
        State(x._1,x._2,x._3,RestoreK(env)::ks,chs)
      }
        case Bind(x,t) => eq.lookup(env(x)) match{
          case Placeholder(i) => State(True, env, eq.addRelation(Placeholder(i), evalCompoundTerm(t,env,eq)), ks, chs)
          case _ => throw new StuckException
        }
        case Is(x,e) => {
          val a = evalArithExp(e, env, eq)
          val p = eq.lookup(env(x))
          p match{
            case Placeholder(n) => {
              State(True, env, eq.addRelation(Placeholder(n), IntValue(a)), ks, chs)
            }
            case _ => throw new StuckException
          }
        }
        case RelationalBody(x1,op,x2) => eq.lookup(env(x1)) match{
          case IntValue(i1) => eq.lookup(env(x2)) match{
            case IntValue(i2) => if (relationalHolds(i1,op,i2)) State(True,env,eq,ks,chs) else State(Fail,env,eq,ks,chs)
            case _ => throw new StuckException
          }
          case _ => throw new StuckException
        }
      case True => 
        (ks,chs) match {
          case (AndK(b2)::rest,_) => State(b2,env,eq,rest,chs)
          case (RestoreK(e)::rest,_) => State(True,e,eq,rest,chs)
          case (Nil,(b2,env2,eq2,ks2)::rest) => State(b2,env2,eq2,ks2,rest)
          case (Nil,Nil) => State(b,env,eq,ks,chs)
          }
      case Fail => 
        chs match {
          case (b2,env2,eq2,ks2)::rest => State(b2,env2,eq2,ks2,rest)
          case Nil => State(b,env,eq,ks,chs)
        }
        case _ => throw new StuckException
        
      }
      
    }
  } // State
              
  def initialState(query: Query): State = {
    val Query(vars, body) = query
    State(body, newScope(vars), EquivClasses(Map()), List(), List())
  }

  def runQuery(query: Query, stateTrans: StateBehavior => Boolean) {
    @scala.annotation.tailrec
    def loop(state: State) {
      val behavior = state.getBehavior
      (behavior, stateTrans(behavior)) match {
        case (NoSolutionNoMoreSolutions | HasSolutionNoMoreSolutions(_), _) => ()
        case (_, true) => loop(state.nextState)
        case _ => ()
      }
    }
    loop(initialState(query))
  } // runQuery
} // Interpreter
