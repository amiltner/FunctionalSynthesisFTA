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

   def len(xs: NatList): Int =
      xs match {
        case Nil => 0
        case Cons(h,t) => len(t) + 1
      }

    def hd(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) => h
      }

    def tl(xs: NatList): Nat =
      xs match {
        case Nil => Z
        case Cons(h,t) =>
                t match {
                    case Nil => h
                    case Cons(t1,t2) => tl(t)
                }
      }

    def remove_hd(xs: NatList): NatList =
      xs match {
        case Nil => Nil
        case Cons(h,t) => t
      }

    def remove_tl(xs: NatList, r: NatList): NatList =
      xs match {
        case Nil => r
        case Cons(h,t) =>
            if (t == Nil) { r }
            else { list_snoc(r,h) }
      }

    def flipped(n: NatList, m: NatList): Boolean =
        if (len(n) == len(m)) {
            if (len(n) == 0) { true }
            else if (hd(n) == tl(m)) {
                flipped(remove_hd(n),remove_tl(m,Nil))
            } else { false }
        } else { false }

    flipped(xs,out)
} }

}