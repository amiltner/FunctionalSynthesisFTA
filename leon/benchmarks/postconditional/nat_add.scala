import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
def nat_add(in1: Nat, in2: Nat): Nat = { choose { (out:Nat) => 

   true

} }

}