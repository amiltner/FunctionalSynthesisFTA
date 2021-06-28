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
  
def nat_iseven(n: Nat): Boolean = { choose { (out:Boolean) => 

   n match {
    case Nil => out = T
    case Cons(h1,t1) => t1 match {
                    case Nil => out = F
                    case Cons(h2,t2) => t2 match {
                                    case Nil => out = T
                                    case Cons(h3,t3) => true
                                    }
                    }
     }

} }

}