import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
sealed abstract class BoolList
case class Cons(head: Boolean, tail: BoolList) extends BoolList
case object Nil extends BoolList
  
def list_even_parity(xs: BoolList): Boolean = { choose { (out:BoolList) => 
    def len(xs: BoolList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => S(len(t))
      }

    def iseven(x: Nat): Boolean =
      x match {
        case Z => T
        case S(n) => n match {
                        case Z => F
                        case S(m) => iseven(m)
                    }
      }

    iseven(len(xs))

} }

}