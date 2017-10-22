package miniprolog.syntax.lowlevel

object Aliases {
  type Name = Symbol
}
import Aliases._

case class Variable(varName: String)

case class Program(clauses: Seq[Clause], query: Query)
case class Query(variables: Set[Variable], body: Body)
case class Clause(name: Name,
                  formalParameters: Seq[Variable],
                  localVariables: Set[Variable],
                  body: Body)
case class CompoundTerm(name: Name, variables: Seq[Variable])

sealed trait Body
case class And(b1: Body, b2: Body) extends Body
case class Choose(b1: Body, b2: Body) extends Body
case class Unify(x1: Variable, x2: Variable) extends Body
case class Call(t: CompoundTerm) extends Body
case class Bind(x: Variable, t: CompoundTerm) extends Body
case class Is(x: Variable, e: ArithExp) extends Body
case class RelationalBody(x1: Variable, op: RelationalOp, x2: Variable) extends Body
case object True extends Body
case object Fail extends Body
case class Print(x: Variable) extends Body

sealed trait ArithExp
case class IntExp(i: Int) extends ArithExp
case class VarExp(x: Variable) extends ArithExp
case class BinExp(e1: ArithExp, op: ArithOp, e2: ArithExp) extends ArithExp

sealed trait ArithOp
case object ArithPlus extends ArithOp
case object ArithMinus extends ArithOp
case object ArithTimes extends ArithOp
case object ArithDiv extends ArithOp

sealed trait RelationalOp
case object LT extends RelationalOp
case object LTE extends RelationalOp
case object GT extends RelationalOp
case object GTE extends RelationalOp
case object EQ extends RelationalOp
case object NEQ extends RelationalOp
