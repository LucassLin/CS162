package miniprolog.translator

import miniprolog.syntax.lowlevel._
import miniprolog.syntax.highlevel._

// set that maintains the ordering it was given
case class OSet[A](revOrder: List[A], set: Set[A]) {
  def +(a: A): OSet[A] = {
    if (set.contains(a)) {
      this
    } else {
      OSet(a :: revOrder, set + a)
    }
  }

  def ++(as: Seq[A]): OSet[A] = {
    as.foldLeft(this)(_ + _)
  }

  lazy val ordered: List[A] = revOrder.reverse
}    

object Translator {
  def varsIn(t: CompoundTerm, accum: OSet[Variable]): OSet[Variable] = {
    accum ++ t.variables
  }

  def varsIn(e: ArithExp, accum: OSet[Variable]): OSet[Variable] = {
    e match {
      case IntExp(_) => accum
      case VarExp(x) => accum + x
      case BinExp(e1, _, e2) => varsIn(e2, varsIn(e1, accum))
    }
  }
  
  def varsIn(b: Body, accum: OSet[Variable]): OSet[Variable] = {
    b match {
      case And(b1, b2) => varsIn(b2, varsIn(b1, accum))
      case Choose(b1, b2) => varsIn(b2, varsIn(b1, accum))
      case Unify(x1, x2) => accum + x1 + x2
      case Call(t) => varsIn(t, accum)
      case Bind(x, t) => varsIn(t, accum + x)
      case Is(x, e) => varsIn(e, accum + x)
      case RelationalBody(x1, _, x2) => accum + x1 + x2
      case True | Fail => accum
      case Print(x) => accum + x
    }
  }

  def varsIn(b: Body): OSet[Variable] = {
    varsIn(b, OSet(List[Variable](), Set[Variable]()))
  }

  def isOneProcedure(clauses: List[FullClause]): Boolean = {
    clauses match {
      case Nil | _ :: Nil => true
      case FullClause(FullFunctor(headName, headParams), _) :: tail => {
        val paramLen = headParams.length
        tail.forall( { case FullClause(FullFunctor(name, params), _) =>
                        headName == name && paramLen == params.length } )
      }
    }
  }
} // Translator

// Moves from the user-facing, high-level syntax to the internal
// mini-prolog syntax.
class Translator {
  // begin instance variables
  private var counter = 0
  // end instance variables

  private def fresh(): String = {
    val retval = counter.toString
    counter += 1
    retval
  }

  private def freshVar(): Variable = {
    Variable(fresh())
  }

  private def freshVariable(): FullVar = {
    FullVar(fresh())
  }

  private def toBody(bodies: List[Body]): Body = {
    bodies match {
      case Nil => True
      case _ => bodies.reduceRight(And.apply)
    }
  }

  private def translateVar(x: FullVar, underscoreSpecial: Boolean = true): Variable = {
    if (underscoreSpecial && x.name == "_") {
      freshVar()
    } else {
      Variable(x.name)
    }
  }

  private def translateFunctor(f: FullFunctor): (CompoundTerm, List[Body]) = {
    val (vars, bodies) = f.params.map(translateTermExp).unzip
    (CompoundTerm(f.name.symbol, vars), bodies.flatten)
  }

  private def translateTermExp(te: FullTermExp): (Variable, List[Body]) = {
    te match {
      case x: FullVar => {
        (translateVar(x), List())
      }
      case FullAtom(symbol) => {
        val x = freshVar()
        (x, List(Bind(x, CompoundTerm(symbol, Seq()))))
      }
      case FullTermNum(n) => {
        val x = freshVar()
        (x, List(Is(x, IntExp(n))))
      }
      case FullTermFunctor(f) => {
        val (term, bodies) = translateFunctor(f)
        val x = freshVar()
        (x, Bind(x, term) :: bodies)
      }
      case TermList(items) => {
        // translate [1,2,3] => cons(1, cons(2, cons(3, nil))), then translate that
        translateTermExp(
          items.foldRight(FullAtom(Symbol("[]")): FullTermExp)((cur, res) =>
            FullTermFunctor(FullFunctor(FullAtom(Symbol(".")), List(cur, res)))))
      }
      case TermListDestruct(head, tail) => {
        // translate [Head|Tail] => cons(Head, Tail), then translate that
        translateTermExp(
          FullTermFunctor(FullFunctor(FullAtom(Symbol(".")), List(head, tail))))
      }
    }
  }

  private def translateRelationalTerm(rt: FullRelationalTerm): (Variable, List[Body]) = {
    rt match {
      case FullExpressionVar(x) => translateTermExp(x)
      case FullExpressionNum(n) => translateTermExp(n)
    }
  }

  private def translateExpressionTerm(et: FullExpressionTerm): (ArithExp, List[Body]) = {
    et match {
      case rt: FullRelationalTerm => {
        val (x, bodies) = translateRelationalTerm(rt)
        (VarExp(x), bodies)
      }
      case FullExpressionBinop(left, op, right) => {
        val (leftVar, leftBodies) = translateExpressionTerm(left)
        val (rightVar, rightBodies) = translateExpressionTerm(right)
        (BinExp(leftVar, op, rightVar), leftBodies ++ rightBodies)
      }
    }
  }

  private def translateBody(b: FullBody): List[Body] = {
    b match {
      case FullAnd(b1, b2) => {
        translateBody(b1) ++ translateBody(b2)
      }
      case FullOr(b1, b2) => {
        List(
          Choose(toBody(translateBody(b1)),
                 toBody(translateBody(b2))))
      }
      case FullUnify(te1, te2) => {
        val (x1, b1) = translateTermExp(te1)
        val (x2, b2) = translateTermExp(te2)
        b1 ++ b2 ++ List(Unify(x1, x2))
      }
      case FullCall(f) => {
        val (compoundTerm, bodies) = translateFunctor(f)
        bodies ++ List(Call(compoundTerm))
      }
      case FullWrite(x) => List(Print(translateVar(x)))
      case FullTrue => List(True)
      case FullFail => List(Fail)
      case FullCompare(rt1, op, rt2) => {
        val (leftVar, leftBodies) = translateRelationalTerm(rt1)
        val (rightVar, rightBodies) = translateRelationalTerm(rt2)
        leftBodies ++ rightBodies ++ List(RelationalBody(leftVar, op, rightVar))
      }
      case FullArithmetic(lhs, exp) => {
        val (leftVar, leftBodies) = translateRelationalTerm(lhs)
        val (expTrans, rightBodies) = translateExpressionTerm(exp)
        val x = freshVar()
        leftBodies ++ rightBodies ++ List(Is(x, expTrans), Unify(x, leftVar))
      }
    }
  }

  private def translateProcedure(clauses: Seq[FullClause]): Clause = {
    assert(clauses.nonEmpty)
    assert(Translator.isOneProcedure(clauses.toList))
    
    // introduce a new variable for each parameter
    val headClause = clauses.head
    val numParams = headClause.head.params.length
    val newFormal = 0.until(numParams).map(_ => freshVariable())

    def clauseBody(clause: FullClause): Body = {
      // unify with each formal param
      val unifications = 
        newFormal.zip(clause.head.params).map(
          { case (newFormal, oldFormal) => FullUnify(newFormal, oldFormal) } )
      toBody(unifications.map(translateBody).flatten.toList ++ translateBody(clause.body))
    }

    val translatedFormal = newFormal.map(x => translateVar(x, false))
    val newClauseBody = clauses.map(clauseBody).reduceRight(Choose.apply)
    Clause(headClause.head.name.symbol,
           translatedFormal,
           Translator.varsIn(newClauseBody).set -- translatedFormal,
           newClauseBody)
  }

  // each returned clause is one procedure
  def translateClauses(clauses: Seq[FullClause]): Seq[Clause] = {
    clauses.groupBy( { case FullClause(FullFunctor(name, params), _) => (name, params.length) })
           .mapValues(translateProcedure)
           .values
           .toSeq
  }

  // returns the translated query along with the ordered list
  // of all variables used in the query
  def translateQuery(q: FullQuery): (Query, Seq[Variable]) = {
    val newBody = toBody(translateBody(q.body))
    val oset = Translator.varsIn(newBody)
    (Query(oset.set, newBody), oset.ordered.toSeq)
  }
} // Translator
    
    
