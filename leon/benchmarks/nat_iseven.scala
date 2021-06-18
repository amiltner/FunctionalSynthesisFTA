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

   true

} }

}