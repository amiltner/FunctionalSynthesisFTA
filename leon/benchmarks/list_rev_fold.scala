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
  
def list_fold(f: (Nat,Nat) => Nat, acc: Nat, xs: NatList): Nat =
  xs match {
    case Nil              => acc
    case Cons(head, tail) => f (list_fold(f, acc, tail), head)
  }
  
def list_snoc(xs: NatList, n: Nat): NatList =
  xs match {
    case Nil             => Cons (n, Nil)
    case Cons(head,tail) => Cons (head, list_snoc(tail,n))
  }
  
def list_rev_fold(xs: NatList): NatList = { choose { (out:NatList) => 

   true

} }

}