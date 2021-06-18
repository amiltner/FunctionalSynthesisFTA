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
    true

} }

}