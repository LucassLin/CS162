package simplescala.polytyped

class IllTyped(val inTypeOf: Boolean) extends Exception {
  def this() {
    this(true)
  }
}

object Aliases {
  type NamedFunctionDefs = Map[FunctionName, (List[TypeVariable], Type, Type)]
  type TypeDefs = Map[UserDefinedTypeName, (List[TypeVariable], Map[ConstructorName, Type])]
  type ConstructorDefs = Map[ConstructorName, UserDefinedTypeName]
  type TypeEnv = Map[Variable, Type]
  type TypeVarsInScope = Set[TypeVariable]
}
import Aliases._

object Typechecker {
  def ensureSet[A](items: Seq[A]) {
    if (items.toSet.size != items.size) {
      throw new IllTyped(false)
    }
  }

  def ensureTypeVarsInScope(ts: Seq[TypeVariable], tau: Type) {
    val asSet = ts.toSet
    def recur(tau: Type) {
      tau match {
        case StringType | BooleanType | IntegerType | UnitType => ()
        case FunctionType(tau1, tau2) => {
          recur(tau1)
          recur(tau2)
        }
        case TupleType(taus) => taus.foreach(recur)
        case UserType(_, taus) => taus.foreach(recur)
        case TypeVariableType(t) if asSet.contains(t) => ()
        case _ => throw new IllTyped(false)
      }
    } // recur

    recur(tau)
  } // ensureTypeVarsInScope

  def makeMap[K, V](ks: List[K], vs: List[V]): Map[K, V] = {
    (ks, vs) match {
      case (Nil, Nil) => Map()
      case (k1 :: k2s, v1 :: v2s) => {
        (makeMap(k2s, v2s)) + (k1 -> v1)
      }
      case _ => throw new IllTyped(false)
    }
  } // makeMap

  def typeReplace(ts: List[TypeVariable], taus1: List[Type], tau2: Type): Type = {
    tau2 match{
      case StringType => tau2
      case BooleanType => tau2
      case IntegerType => tau2
      case UnitType => tau2
      case TypeVariableType(t: TypeVariable) => if(ts.contains(t)) makeMap(ts, taus1)(t) else throw new IllTyped(false)
      case FunctionType(t1: Type, t2: Type) => FunctionType(typeReplace(ts, taus1, t1), typeReplace(ts, taus1, t2))
      case TupleType(taus: List[Type]) => TupleType(typeReplaceHelperList(makeMap(ts, taus1), taus))
      case UserType(un: UserDefinedTypeName, taus: List[Type]) => UserType(un, typeReplaceHelperList(makeMap(ts, taus1), taus))
    }
  } // typeReplace

  def typeReplaceHelper(m: Map[TypeVariable, Type], tau: Type): Type = {
    tau match{
      case StringType => StringType
      case BooleanType => BooleanType
      case IntegerType => IntegerType
      case UnitType => UnitType
      case FunctionType(t1: Type, t2: Type) => FunctionType(typeReplaceHelper(m, t1), typeReplaceHelper(m, t2))
      case TupleType(taus: List[Type]) => TupleType(typeReplaceHelperList(m, taus))
      case UserType(un: UserDefinedTypeName, taus: List[Type]) => UserType(un, typeReplaceHelperList(m, taus))
      case TypeVariableType(t: TypeVariable) => m(t)
    }
  } // typeReplaceHelper

  def typeReplaceHelperList(m: Map[TypeVariable, Type], taus: List[Type]): List[Type] = {
    taus match {
      case Nil => Nil
      case x::xs => typeReplaceHelper(m, x)::typeReplaceHelperList(m, xs)
    }
    
  } // typeReplaceHelperList

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

  def asSingleton[A](as: List[A]): A = {
    as match {
      case a :: Nil => a
      case a1 :: a2 :: rest if a1 == a2 => {
        asSingleton(a2 :: rest)
      }
      case _ => throw new IllTyped(false)
    }
  } // asSingleton

  def apply(p: Program): Type = {
    ensureSet(p.defs.map(_.fn))
    p.defs.foreach(d => ensureSet(d.ts))
    ensureSet(p.tdefs.map(_.un))
    ensureSet(p.tdefs.flatMap(_.cdefs.map(_.cn)))
    p.tdefs.foreach(td => ensureSet(td.ts))
    p.tdefs.foreach(td =>
      td.cdefs.foreach(cd =>
        ensureTypeVarsInScope(td.ts, cd.tau)))
    p.defs.foreach(d => {
      ensureTypeVarsInScope(d.ts, d.tau1)
      ensureTypeVarsInScope(d.ts, d.tau2)
    })
      
    val fdefs = p.defs.map( { case Def(fn, ts, _, tau1, tau2, _) => (fn -> (ts, tau1, tau2)) } ).toMap
    val tdefs = p.tdefs.map(
      { case UserDefinedTypeDef(un, ts, cdefs) =>
          (un -> (ts -> cdefs.map(
            { case ConstructorDefinition(cn, tau) => (cn -> tau) }).toMap)) }).toMap
    val cdefs = p.tdefs.flatMap(
      { case UserDefinedTypeDef(un, _, cdefs) => cdefs.map(
          { case ConstructorDefinition(cn, _) => (cn -> un) } ) } ).toMap
    val checker = new Typechecker(fdefs, tdefs, cdefs)
    p.defs.foreach(checker.checkDef)
    checker.typeof(p.e)
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
  import Typechecker._

  def checkDef(theDef: Def) {
    new InTypeScope(theDef.ts.toSet).checkDef(theDef)
  }

  def typeof(exp: Exp): Type = {
    new InTypeScope(Set()).typeof(exp, Map())
  }

  class InTypeScope(val tscope: TypeVarsInScope) {
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
    // needs 19 lines of code to implement, and most rules need only
    // 3 - 8 lines of code.  If you start consistently needing a lot
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
        case (FunctionExp(x, t, e), gamma) => if(typeOk(t)) FunctionType(t, typeof(e, gamma + (x->t))) else throw new IllTyped(false)
	case (AnonCallExp(e1, e2), gamma) => typeof(e1, gamma) match {
          case FunctionType(t1, t2)  if (typeof(e2, gamma) == t1 ) => t2
          case _ => throw new IllTyped(false)
        }
	case (NamedCallExp(fn, taus, e), gamma) => 
          if (typeOkList(taus) && fdefs.contains(fn) && (fdefs(fn)._1).length == taus.length && typeof(e, gamma) == typeReplace(fdefs(fn)._1, taus, fdefs(fn)._2))
            typeReplace(fdefs(fn)._1, taus, fdefs(fn)._3)
          else throw new IllTyped(false)
        case (IfExp(e1, e2, e3), gamma) =>if(typeof(e1, gamma) == BooleanType && typeof(e2, gamma) == typeof(e3, gamma)) typeof(e2, gamma) else throw new IllTyped(false)
	case (BlockExp(vals, e), gamma) => typeof(e, blockGamma(vals, gamma))
        case (TupleExp(es), gamma) => TupleType(tupleTypes(es, gamma))
	case (AccessExp(e, n), gamma) => typeof(e, gamma) match {
          case TupleType(t1) => tupleAccess(t1, n)
	  case _ => throw new IllTyped(false)
        }
	case (ConstructorExp(cn, t1, e), gamma) => 
          if(typeOkList(t1) && cdefs.contains(cn) && (tdefs(cdefs(cn))._1).length == t1.length && typeof(e, gamma) == typeReplace(tdefs(cdefs(cn))._1, t1, (tdefs(cdefs(cn))._2)(cn)))
            UserType(cdefs(cn), t1)
          else throw new IllTyped(false)
    	case (MatchExp(e1, a), gamma) => typeof(e1, gamma) match {
          case UserType(un, t1) => if(tdefs.contains(un) && casesSane(a, un) && (tdefs(un)._1).length == t1.length)
            asSingleton(casesTypes(a, gamma, tdefs(un)._1, t1, tdefs(un)._2))  
            else throw new IllTyped(false)
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
    } // tupleTypes

    def casesTypes(cases: List[Case], gamma: TypeEnv, ts: List[TypeVariable], taus1: List[Type], m: Map[ConstructorName, Type]): List[Type] = {
      cases match {
        case Nil => Nil
        case ConstructorCase(cn, x, e) :: cases => {
          val tau2 = m(cn)
          val tau2P = typeReplace(ts, taus1, tau2)
          val tau3 = typeof(e, gamma + (x -> tau2P))
          tau3 :: casesTypes(cases, gamma, ts, taus1, m)
        }
        case _ => throw new IllTyped(false)
      }
    } // casesTypes

    def typeOkList(taus: List[Type]): Boolean = {
      taus.forall(typeOk)
    } // typeOkList

    def typeOk(tau: Type): Boolean = {
      tau match {
        case StringType | BooleanType | IntegerType | UnitType => true
        case FunctionType(tau1, tau2) => typeOk(tau1) && typeOk(tau2)
        case TupleType(taus) => typeOkList(taus)
        case UserType(_, taus) => typeOkList(taus)
        case TypeVariableType(tv) => tscope.contains(tv)
      }
    } // typeOk
  } // InTypeScope

  def casesSane(cases: List[Case], un: UserDefinedTypeName): Boolean = {
    val (ts, m) = tdefs(un)
    casesSaneHelper(cases, Set(), m)
  } // casesSane
} // Typechecker
