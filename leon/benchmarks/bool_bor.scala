import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
def bool_bor(p: Boolean, q: Boolean): Boolean = { choose { (out:Boolean) => 

// (((p == T) && (q == T)) ==> (out == T)) &&
   (((p == T) && (q == F)) ==> (out == T)) &&
   (((p == F) && (q == T)) ==> (out == T)) &&
   (((p == F) && (q == F)) ==> (out == F)) &&
   true

} }

}