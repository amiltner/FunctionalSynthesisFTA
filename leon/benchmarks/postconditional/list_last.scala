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
  
sealed abstract class NatOpt
case class Some(nat: Nat) extends NatOpt
case object None extends NatOpt
  
def list_last(xs: NatList): NatOpt = { choose { (out:NatOpt) => 

   true

} }

}