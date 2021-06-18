import leon.lang._
import leon.lang.synthesis._
import leon._

object Compiler {
  abstract class Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class Minus(lhs: Expr, rhs: Expr) extends Expr
  case class UMinus(e: Expr) extends Expr
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr
  case class And(lhs: Expr, rhs: Expr) extends Expr
  case class Implies(lhs: Expr, rhs: Expr) extends Expr
  case class Or(lhs: Expr, rhs: Expr) extends Expr
  case class Not(e : Expr) extends Expr
  case class Eq(lhs: Expr, rhs: Expr) extends Expr
  case class Ite(cond: Expr, thn: Expr, els: Expr) extends Expr
  case class BoolLiteral(b : Boolean) extends Expr
  case class IntLiteral(i: BigInt) extends Expr

  def exists(e: Expr, f: Expr => Boolean): Boolean = {
    f(e) || (e match {
      case Plus(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Minus(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case LessThan(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case And(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Or(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Implies(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Eq(lhs, rhs) => exists(lhs, f) || exists(rhs, f)
      case Ite(c, t, e) => exists(c, f) || exists(t, f) || exists(e, f)
      case Not(e) => exists(e, f)
      case UMinus(e) => exists(e, f)
      case _ => false
    })
  }

  abstract class Value
  case class BoolValue(b: Boolean) extends Value
  case class IntValue(i: BigInt) extends Value
  case object Error extends Value

  def eval(e: Expr): Value = e match {
    case Plus(l, r) =>
      (eval(l), eval(r)) match {
        case (IntValue(il), IntValue(ir)) => IntValue(il+ir)
        case _ => Error
      }

    case Minus(l, r) =>
      (eval(l), eval(r)) match {
        case (IntValue(il), IntValue(ir)) => IntValue(il-ir)
        case _ => Error
      }

    case UMinus(l) =>
      eval(l) match {
        case IntValue(b) => IntValue(-b)
        case _ => Error
      }

    case LessThan(l, r) =>
      (eval(l), eval(r)) match {
        case (IntValue(il), IntValue(ir)) => BoolValue(il < ir)
        case _ => Error
      }

    case And(l, r) =>
      eval(l) match {
        case b @ BoolValue(false) => b
        case b: BoolValue =>
          eval(r)
        case _ =>
          Error
      }

    case Or(l, r) =>
      eval(l) match {
        case b @ BoolValue(true) =>
          b
        case b: BoolValue =>
          eval(r)
        case _ =>
          Error
      }

    case Implies(l, r) =>
      eval(l) match {
        case b @ BoolValue(true) =>
          eval(r)
        case b @ BoolValue(false) =>
          BoolValue(true)
        case _ => Error
      }

    case Not(l) =>
      eval(l) match {
        case BoolValue(b) => BoolValue(!b)
        case _ => Error
      }

    case Eq(l, r) =>
      (eval(l), eval(r)) match {
        case (IntValue(il), IntValue(ir))   => BoolValue(il == ir)
        case (BoolValue(il), BoolValue(ir)) => BoolValue(il == ir)
        case _ => Error
      }

    case Ite(c, t, e) =>
      eval(c) match {
        case BoolValue(true) => eval(t)
        case BoolValue(false) => eval(t)
        case _ => Error
      }

    case IntLiteral(l)  => IntValue(l)
    case BoolLiteral(b) => BoolValue(b)
  }


  def desugar(in: Expr): Expr = {
    choose{ (out: Expr) =>
      eval(in) == eval(out) && !(out.isInstanceOf[Implies])
    }
  }
}
