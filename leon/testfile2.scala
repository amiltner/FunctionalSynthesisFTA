import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Insert {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List

  def size(l: List) : BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, t) => 1 + size(t)
  })

  def insert(in1 : List, v : BigInt): List =
  {
  require(sorted(in1))
  (in1 match {
    case Nil => Cons (v, Nil)
    case Cons(w, in2) => if (v < w) Cons (v,in1) else if (v == w) in1 else Cons (w, insert(in2,v))
  })
  } ensuring(sorted(_))
  
  def delete(in1 : List, v : BigInt): List = 
  {
    require(sorted(in1))
    (in1 match {
    case Nil => Nil
    case Cons(w, in2) => if (v == w) in2 else if (v < w) in1 else Cons(w, delete(in2,v))
  })
  } ensuring(sorted(_))
  
  def lookup(in1 : List, v : BigInt): Boolean =
  {
    require(sorted(in1))
    (in1 match {
      case Nil => false
      case Cons(w, in2) => if (v == w) true else if (v < w) false else lookup(in2,v)
    })
  }
  
  def sortedprime(in1 : List, i : BigInt) : Boolean =
  {
    (in1 match {
      case Nil => true
      case Cons(w,in2) => i < w && sortedprime(in2,w)
    })
  }
  
  def sorted(in1 : List) : Boolean = (in1 match {
    case Nil => true
    case Cons(v, in2) => sortedprime(in2,v)
  })
  
  def safedeleteins(in1 : List, x : BigInt) : Boolean =
  {
    require(sorted(in1))
    !(lookup(delete(in1,x),x))
  } holds
}

