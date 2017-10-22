package simplescala.interpreter

case class Nat(n: Int) {
  assert(n >= 0)

  def -(other: Nat): Nat = {
    Nat(n - other.n)
  }

  def -(other: Int): Nat = {
    this - Nat(other)
  }
}

case class Variable(name: String)
case class FunctionName(name: String)
case class ConstructorName(name: String)

sealed trait Exp
case class VariableExp(x: Variable) extends Exp
case class StringExp(str: String) extends Exp
case class BooleanExp(b: Boolean) extends Exp
case class IntExp(i: Int) extends Exp
case object UnitExp extends Exp
case class BinopExp(e1: Exp, op: Binop, e2: Exp) extends Exp
case class FunctionExp(x: Variable, e: Exp) extends Exp
case class AnonCallExp(e1: Exp, e2: Exp) extends Exp
case class NamedCallExp(fn: FunctionName, e: Exp) extends Exp
case class IfExp(e1: Exp, e2: Exp, e3: Exp) extends Exp
case class BlockExp(vals: List[Val], e: Exp) extends Exp
case class TupleExp(es: List[Exp]) extends Exp
case class AccessExp(e: Exp, n: Nat) extends Exp
case class ConstructorExp(cn: ConstructorName, e: Exp) extends Exp
case class MatchExp(e: Exp, cases: List[Case]) extends Exp

case class Val(x: Variable, e: Exp)

sealed trait Case
case class ConstructorCase(cn: ConstructorName, x: Variable, e: Exp) extends Case
case class TupCase(xs: List[Variable], e: Exp) extends Case

sealed trait Binop
case object BinopPlus extends Binop
case object BinopMinus extends Binop
case object BinopTimes extends Binop
case object BinopDiv extends Binop
case object BinopAnd extends Binop
case object BinopOr extends Binop
case object BinopLT extends Binop
case object BinopLTE extends Binop

case class Def(fn: FunctionName, x: Variable, e: Exp)

case class Program(defs: Seq[Def], e: Exp)

