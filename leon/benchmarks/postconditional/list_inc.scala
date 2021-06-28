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
  
def list_map(xs: NatList, f: (Nat) => Nat): NatList =
  xs match {
    case Nil              => Nil
    case Cons(head, tail) => Cons (f(head), list_map(tail,f))
  }
  
def list_inc(xs: NatList): NatList = { choose { (out:NatList) => 

   def contained_in(x:Nat,xs:NatList) : Boolean =
      xs match {
        case Nil => false
        case Cons(h,t) =>
          if (h == x) {
            true
          } else {
            contained_in(x,t)
          }
      }

    def full_contained_in_inc(xs:NatList,ys:NatList) : Boolean =
      xs match {
        case Nil => true
        case Cons(h,t) =>
          if (contained_in(S(h),ys)) {
            full_contained_in(t,ys)
          } else {
            false
          }
      }

    full_contained_in(xs,out)

} }

}