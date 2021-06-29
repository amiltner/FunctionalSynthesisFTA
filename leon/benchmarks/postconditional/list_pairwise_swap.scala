import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat

sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
sealed abstract class NatList
case class Cons(head: Nat, tail: NatList) extends NatList
case object Nil extends NatList
  
def list_pairwise_swap(xs: NatList): NatList = { choose { (out:NatList) => 

   def len(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => S(len(t))
      }

    def isodd(x: Nat): Boolean =
      x match {
        case Z => F
        case S(n) => n match {
                        case Z => T
                        case S(m) => isodd(m)
                    }
      }

    ((isodd(len(xs)) == T) && (out == Nil)) || (isodd(len(xs)) == F)

} }

}