package miniprolog.syntax.highlevel

import miniprolog.syntax.lowlevel.{ArithOp, RelationalOp}

case class FullFunctor(name: FullAtom, params: List[FullTermExp])

sealed trait FullTermExp
case class FullVar(name: String) extends FullTermExp
case class FullAtom(symbol: Symbol) extends FullTermExp
case class FullTermFunctor(f: FullFunctor) extends FullTermExp
case class TermList(items: List[FullTermExp]) extends FullTermExp
case class TermListDestruct(head: FullTermExp, tail: FullTermExp) extends FullTermExp
case class FullTermNum(num: Int) extends FullTermExp

sealed trait FullRelationalTerm
sealed trait FullExpressionTerm
case class FullExpressionVar(v: FullVar) extends FullExpressionTerm with FullRelationalTerm
case class FullExpressionNum(i: FullTermNum) extends FullExpressionTerm with FullRelationalTerm
case class FullExpressionBinop(lhs: FullExpressionTerm, op: ArithOp, rhs: FullExpressionTerm) extends FullExpressionTerm

sealed trait FullBody
case class FullAnd(b1: FullBody, b2: FullBody) extends FullBody
case class FullOr(b1: FullBody, b2: FullBody) extends FullBody
case class FullUnify(te1: FullTermExp, te2: FullTermExp) extends FullBody
case class FullCall(f: FullFunctor) extends FullBody
case class FullWrite(v: FullVar) extends FullBody
case object FullTrue extends FullBody
case object FullFail extends FullBody
case class FullCompare(rt1: FullRelationalTerm, op: RelationalOp, rt2: FullRelationalTerm) extends FullBody
case class FullArithmetic(lhs: FullRelationalTerm, expr: FullExpressionTerm) extends FullBody

case class FullClause(head: FullFunctor, body: FullBody)
case class FullQuery(body: FullBody)
