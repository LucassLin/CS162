package simplescala.polytyped

import simplescala.interpreter.{Value,
                                StrV,
                                BoolV,
                                IntV,
                                UnitV,
                                ClosureV,
                                ConstructorV,
                                TupleV}

object TestValue {
  def quoteString(s: String): String = "\"" + s + "\""

  def prettyString(v: Value): String = {
    v match {
      case StrV(s) => quoteString(s)
      case BoolV(b) => b.toString
      case IntV(i) => i.toString
      case UnitV => "unit"
      case ClosureV(x, e, env) => {
        "closure" + Seq(x, e, env).mkString("(", ", ", ")")
      }
      case ConstructorV(ConstructorName(name), v) => {
        name + "(" + prettyString(v) + ")"
      }
      case TupleV(vs) => {
        vs.map(prettyString).mkString("(", ", ", ")")
      }
    }
  } // prettyString
} // TestValue

sealed trait TestExpect
case object ExpectIllTyped extends TestExpect
case class ExpectWellTypedStuck(theType: Type) extends TestExpect
case class ExpectWellTypedValue(tv: TestValue, theType: Type) extends TestExpect

sealed trait TestValue {
  // returns true if they are the same, else false
  def compareToValue(v: Value): Boolean
  def prettyString(): String

  // returns None if they are the same, else an error
  // message describing what happened
  def compareString(v: Value): Option[String] = {
    if (compareToValue(v)) {
      None
    } else {
      Some("EXPECTED: " + prettyString + "\n" +
           "RECEIVED: " + TestValue.prettyString(v))
    }
  } // compareString
}
case class TestString(s: String) extends TestValue {
  def compareToValue(v: Value): Boolean = {
    v match {
      case StrV(`s`) => true
      case _ => false
    }
  }
  def prettyString(): String = TestValue.quoteString(s)
}
case class TestBoolean(b: Boolean) extends TestValue {
  def compareToValue(v: Value): Boolean = {
    v match {
      case BoolV(`b`) => true
      case _ => false
    }
  }
  def prettyString(): String = b.toString
}
case class TestInt(i: Int) extends TestValue {
  def compareToValue(v: Value): Boolean = {
    v match {
      case IntV(`i`) => true
      case _ => false
    }
  }
  def prettyString(): String = i.toString
}
case object TestUnit extends TestValue {
  def compareToValue(v: Value): Boolean = {
    v match {
      case UnitV => true
      case _ => false
    }
  }
  def prettyString(): String = "unit"
}
case class TestConstructor(cn: ConstructorName, tv: TestValue) extends TestValue {
  def compareToValue(v: Value): Boolean = {
    v match {
      case ConstructorV(`cn`, v) => tv.compareToValue(v)
      case _ => false
    }
  }
  def prettyString(): String = cn.name + "(" + tv.prettyString + ")"
}
case class TestTuple(tvs: List[TestValue]) extends TestValue {
  def compareToValue(v: Value): Boolean = {
    v match {
      case TupleV(vs) if tvs.size == vs.size => {
        tvs.zip(vs).forall( { case (tv, v) => tv.compareToValue(v) } )
      }
      case _ => false
    }
  }
  def prettyString(): String = tvs.map(_.prettyString).mkString("(", ", ", ")")
}
