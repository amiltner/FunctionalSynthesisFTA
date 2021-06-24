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

sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
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
  
def list_sorted_insert(xs: NatList, n: Nat): NatList = { choose { (out:NatList) => 

   def list_sorted(xs: NatList) : Boolean =
        xs match {
            Nil => T
            Cons(h,t) => t match {
                            Nil => list_sorted(t)
                            Cons(t1,t2) =>
                                    if (nat_compare(h,t1) != GT) {
                                        list_sorted(t)
                                    } else {
                                        F
                                    }
                        }
        }

    def contained_in(x:Nat,xs:NatList) : Boolean =
      xs match {
        case Nil => false
        case Cons(h,t) =>
          if (h == x) {
            true
          } else {
            contained_in(x,t)
          }
      }

    def full_contained_in(xs:NatList,ys:NatList) : Boolean =
      xs match {
        case Nil => true
        case Cons(h,t) =>
          if (contained_in(h,ys)) {
            full_contained_in(t,ys)
          } else {
            false
          }
      }

    list_sorted(out) && full_contained_in(Cons(n,xs),out)

} }

}