package simplescala.simplytyped

class IllTyped(val inTypeOf: Boolean) extends Exception {
  def this() {
    this(true)
  }
}

object Aliases {
  type NamedFunctionDefs = Map[FunctionName, (Type, Type)]
  type TypeDefs = Map[UserDefinedTypeName, Map[ConstructorName, Type]]
  type ConstructorDefs = Map[ConstructorName, UserDefinedTypeName]
  type TypeEnv = Map[Variable, Type]
}
import Aliases._

object Typechecker {
  def ensureSet[A](items: Seq[A]) {
    if (items.toSet.size != items.size) {
      throw new IllTyped(false)
    }
  }

  def apply(p: Program): Type = {
    ensureSet(p.defs.map(_.fn))
    ensureSet(p.tdefs.map(_.un))
    ensureSet(p.tdefs.flatMap(_.cdefs.map(_.cn)))

    val fdefs = p.defs.map( { case Def(fn, _, tau1, tau2, _) => (fn -> (tau1 -> tau2)) } ).toMap
    val tdefs = p.tdefs.map(
      { case UserDefinedTypeDef(un, cdefs) => (un -> cdefs.map(
          { case ConstructorDefinition(cn, tau) => (cn -> tau) } ).toMap) } ).toMap
    val cdefs = p.tdefs.flatMap(
      { case UserDefinedTypeDef(un, cdefs) => cdefs.map(
          { case ConstructorDefinition(cn, _) => (cn -> un) } ) } ).toMap
    val checker = new Typechecker(fdefs, tdefs, cdefs)
    p.defs.foreach(checker.checkDef)
    checker.typeof(p.e, Map())
  } // apply

  def eitherType(p: Program): Either[IllTyped, Type] = {
    try {
      Right(apply(p))
    } catch {
      case e: IllTyped => Left(e)
    }
  }
} // Typechecker

class Typechecker(val fdefs: NamedFunctionDefs,
                  val tdefs: TypeDefs,
                  val cdefs: ConstructorDefs) {
  def checkDef(theDef: Def) {
    if (typeof(theDef.e, Map(theDef.x -> theDef.tau1)) != theDef.tau2) {
      throw new IllTyped(false)
    }
  }

  // Recommendation: the first thing you should do is figure
  // out exactly which rule currently applies.  This will
  // require you to pattern match on the expression, and potentially
  // check additional things as well.
  //
  // As a hint, in our reference implementation, the longest rule
  // needs 13 lines of code to implement, and most rules need only
  // 3 - 7 lines of code.  If you start consistently needing a lot
  // more code than that, you should revisit your general design.
  //
  // All the helper functions have been provided for you; you need only
  // implement the typing rules in `typeof` below.
  def typeof(exp: Exp, gamma: TypeEnv): Type = {
   (exp, gamma) match{
        case (BooleanExp(b), gamma) => BooleanType
        case (StringExp(s), gamma) => StringType
        case (VariableExp(x), gamma) if (gamma.contains(x)) => gamma(x) 
        case (IntExp(i), gamma) => IntegerType
        case (UnitExp, gamma) => UnitType
        case (BinopExp(e1, op, e2), gamma) => typeof(e1, gamma) match{
          case IntegerType => typeof(e2, gamma) match{
            case IntegerType => op match{
              case BinopMinus => IntegerType
              case BinopTimes => IntegerType
              case BinopDiv => IntegerType
              case BinopLT => BooleanType
              case BinopLTE => BooleanType
              case BinopPlus => IntegerType
              case _ => throw new IllTyped(false)
            }
	    case _ => throw new IllTyped(false)
          }
          case StringType => typeof(e2, gamma) match{
            case StringType => op match{
              case BinopPlus => StringType
              case _ => throw new IllTyped(false)
            }
	    case _ => throw new IllTyped(false)
          }
          case BooleanType => typeof(e2, gamma) match{
            case BooleanType => op match{
              case BinopAnd => BooleanType
              case BinopOr => BooleanType
              case _ => throw new IllTyped(false)
            }
	    case _ => throw new IllTyped(false)
          }
	  case _ => throw new IllTyped(false)
        }
        case (AnonCallExp(e1, e2), gamma) => typeof(e1, gamma) match {
          case FunctionType(t1, t2)  if (typeof(e2, gamma) == t1 ) => t2
	  case _ => throw new IllTyped(false)
        }
        case (FunctionExp(x, t, e), gamma) => FunctionType(t, typeof(e, gamma + (x->t)))
        case (NamedCallExp(fn, e), gamma) => if (fdefs.contains(fn) && fdefs(fn)._1 == typeof(e, gamma)) fdefs(fn)._2 else throw new IllTyped(false)
        case (IfExp(e1, e2, e3), gamma) =>if(typeof(e1, gamma) == BooleanType && typeof(e2, gamma) == typeof(e3, gamma)) typeof(e2, gamma) else throw new IllTyped(false)
        case (BlockExp(vals, e), gamma) => typeof(e, blockGamma(vals, gamma))
        case (TupleExp(es), gamma) => TupleType(tupleTypes(es, gamma))
        case (AccessExp(e, n), gamma) => typeof(e, gamma) match {
          case TupleType(t1) => tupleAccess(t1, n)
	  case _ => throw new IllTyped(false)
        }
        //case (ConstructorExp(cn, e), gamma) if(cdefs.contains(cn) && typeof(e, gamma) == (tdefs(cdefs(cn))(cn))) => UserType(cdefs(cn))
        case (ConstructorExp(cn, e), gamma) if(cdefs.contains(cn))
            => cdefs(cn) match {
              case un => if ((tdefs(un))(cn) == typeof(e, gamma))  UserType(un) else throw new IllTyped(false)
            }
	//case (MatchExp(e1, cases), gamma) => typeof(e1, gamma) match {
          //case UserType(un) if(tdefs.contains(un) && casesSane(cases, un)) => asSingleton(casesTypes(cases, gamma, tdefs(un)))
        //}
	case (MatchExp(e1, a), gamma) => typeof(e1, gamma) match {
          case UserType(un) => if(tdefs.contains(un) && casesSane(a, un)) asSingleton(casesTypes(a, gamma, tdefs(un))) else throw new IllTyped(false)
          case TupleType(t1) => a match{
            case List(TupCase(xs, e2)) => if(t1.length == xs.length) typeof(e2, tupGamma(xs, t1, gamma)) else throw new IllTyped(false)
	    case _ => throw new IllTyped(false)
          }
	  case _ => throw new IllTyped(false)
        }
	case _ => throw new IllTyped(false)




      }
  } // typeof

  def blockGamma(vals: List[Val], gamma: TypeEnv): TypeEnv = {
    vals match {
      case Nil => gamma
      case Val(x, e) :: vals => {
        val tau = typeof(e, gamma)
        blockGamma(vals, gamma + (x -> tau))
      }
    }
  } // blockGamma

  def tupleTypes(exps: List[Exp], gamma: TypeEnv): List[Type] = {
    exps match {
      case Nil => Nil
      case e1 :: e2s => {
        typeof(e1, gamma) :: tupleTypes(e2s, gamma)
      }
    }
  }

  def tupleAccess[A](as: List[A], n: Nat): A = {
    (as, n) match {
      case (a1 :: a2, Nat(1)) => a1
      case (a1 :: a2, Nat(n)) if n > 1 => tupleAccess(a2, Nat(n - 1))
      case _ => throw new IllTyped(false)
    }
  } // tupleAccess

  def tupGamma(xs: List[Variable], taus: List[Type], gamma: TypeEnv): TypeEnv = {
    (xs, taus) match {
      case (Nil, Nil) => gamma
      case (x1 :: x2, tau1 :: tau2) => {
        tupGamma(x2, tau2, gamma + (x1 -> tau1))
      }
      case _ => throw new IllTyped(false)
    }
  } // tupGamma

  def casesSane(cases: List[Case], un: UserDefinedTypeName): Boolean = {
    casesSaneHelper(cases, Set(), tdefs(un))
  } // casesSane

  def casesSaneHelper(cases: List[Case], cnBar: Set[ConstructorName], m: Map[ConstructorName, Type]): Boolean = {
    cases match {
      case Nil => m.keySet == cnBar
      case ConstructorCase(cn1, x, e) :: cases => {
        (m.contains(cn1) &&
         !cnBar.contains(cn1) &&
         casesSaneHelper(cases, cnBar + cn1, m))
      }
      case _ => false
    }
  } // casesSaneHelper

  def casesTypes(cases: List[Case], gamma: TypeEnv, m: Map[ConstructorName, Type]): List[Type] = {
    cases match {
      case Nil => Nil
      case ConstructorCase(cn, x, e) :: cases => {
        val tau1 = m(cn)
        val tau2 = typeof(e, gamma + (x -> tau1))
        tau2 :: casesTypes(cases, gamma, m)
      }
      case _ => throw new IllTyped(false)
    }
  } // casesTypes

  def asSingleton[A](as: List[A]): A = {
    as match {
      case a :: Nil => a
      case a1 :: a2 :: rest if a1 == a2 => {
        asSingleton(a2 :: rest)
      }
      case _ => throw new IllTyped(false)
    }
  } // asSingleton
} // Typechecker
