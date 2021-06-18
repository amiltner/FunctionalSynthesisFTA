import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class NatList
case class Cons(head: Nat, tail: NatList) extends NatList
case object Nil extends NatList
  
sealed abstract class Cmp
case object LT extends Cmp
case object EQ extends Cmp
case object GT extends Cmp
  
def nat_compare(n1: Nat, n2: Nat): Cmp =
  n1 match {
    case Z =>
      n2 match {
        case Z    => EQ
        case S(_) => LT
      }
    case S(m1) =>
      n2 match {
        case Z     => GT
        case S(m2) => nat_compare(m1, m2)
      }
  }
  
def list_insert(xs: NatList, n: Nat): NatList =
  xs match {
    case Nil =>
      Cons (n, Nil)
    case Cons(head, tail) =>
      nat_compare(n, head) match {
        case LT => Cons (n, xs)
        case EQ => xs
        case GT => Cons (head, list_insert(tail, n))
      }
  }
  
def list_sort_sorted_insert(xs: NatList): NatList = { choose { (out:NatList) => 

   true

} }

}
