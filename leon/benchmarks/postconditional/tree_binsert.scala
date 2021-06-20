import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Nat
case class S(nat: Nat) extends Nat
case object Z extends Nat
  
sealed abstract class Cmp
case object LT extends Cmp
case object EQ extends Cmp
case object GT extends Cmp
  
sealed abstract class NatTree
case object Leaf extends NatTree
case class Node(left: NatTree, n: Nat, right: NatTree) extends NatTree
  
def nat_compare(n1: Nat, n2: Nat): Cmp =
  n1 match {
    case Z =>
      n2 match {
        case Z    => EQ
        case S(_) => LT
      }
    case S(m1) =>
      n2 match {
        case Z     => GT
        case S(m2) => nat_compare(m1, m2)
      }
  }
  
def tree_binsert(t: NatTree,x: Nat): NatTree = { choose { (out:NatTree) => 

   true

} }

}