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

sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
def list_stutter(n: Nat,m: Nat): NatList = { choose { (out:NatList) => 

   def len(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => S(len(t))
      }

    def hd(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => h
      }

    def all_n(n: Nat,xs: NatList): Boolean =
        xs match {
            case Nil => T
            case Cons(h,t) =>
                    if (h == n) {
                        all_n(n,t)
                    } else { F }
        }

    (len(out) == m) && (all_n(n,out) == T)

} }

}