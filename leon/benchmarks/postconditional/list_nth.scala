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
  
def list_nth(xs: NatList, n: Nat): Nat = { choose { (out:Nat) => 

   def len(xs: NatList): Int =
      xs match {
        case Nil => 0
        case Cons(h,t) => nat_compare(t) + 1
      }

    def nat_to_int(x: Nat): Int =
      x match {
        case Z => 0
        case S(m) => nat_to_int(m) + 1
      }

    def hd(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => h
      }

    ( (len(xs) < nat_to_int(n)) && (out = Z) ) || ( (n = Z) && (out = hd(xs) )

} }

}