import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Delete {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List
  
  sealed abstract class ListRecursion
  case class ConsR(head: BigInt, tail: (BigInt,Boolean)) extends ListRecursion
  case object NilR extends ListRecursion
  
  def foldList(l: List, lr: ListRecursion => (BigInt,Boolean)) : (BigInt,Boolean) =
  (l match {
    case Nil => lr(NilR)
    case Cons(h, t) => lr(ConsR(h, foldList(t,lr)))
  })
  
  
  def size(l: List) : BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)
  
  def inv(l : List): (Option[BigInt],Boolean) =  {
    ???
  } ensuring {
    (res : (Option[BigInt],Boolean)) =>
      if (l == Cons(1,Nil)) {res._2 == true} 
      else if (l == Cons(0,Cons(1,Nil))) {res._2 == true}
      else if (l == Cons(0,Cons(2,Nil))) {res._2 == true}
      else if (l == Cons(1,Cons(2,Nil))) {res._2 == true}
      else if (l == Cons(1,Cons(2,Cons(3,Nil)))) {res._2 == true}
      else if (l == Cons(1,Cons(1,Nil))) {res._2 == false}
      else if (l == Cons(0,Cons(0,Nil))) {res._2 == false}
      else if (l == Cons(2,Cons(2,Nil))) {res._2 == false}
      else if (l == Cons(0,Cons(1,Cons(1,Nil)))) {res._2 == false}
      else if (l == Cons(1,Cons(2,Cons(2,Nil)))) {res._2 == false}
      else {true}
  } 
}

