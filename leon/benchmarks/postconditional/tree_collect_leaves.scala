import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Blah {
  
sealed abstract class Boolean
case object T extends Boolean
case object F extends Boolean
  
sealed abstract class BooleanTree
case object Leaf extends BooleanTree
case class Node(left: BooleanTree, n: Boolean, right: BooleanTree) extends BooleanTree
  
sealed abstract class BooleanList
case class Cons(head: Boolean, tail: BooleanList) extends BooleanList
case object Nil extends BooleanList
  
def list_append(l1: BooleanList, l2: BooleanList): BooleanList =
  l1 match {
    case Nil              => l2
    case Cons(head, tail) => Cons (head, list_append(tail, l2))
  }

def tree_collect_leaves(t: BooleanTree): BooleanList = { choose { (out:BooleanList) => 

   true

} }

}