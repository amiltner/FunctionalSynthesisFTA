import leon.lang._

object ObjectParamMutation10 {

  case class A(var x: Int)

  def f1(a1: A, a2: A): Int = {
    a2.x = a1.x
    a1.x = 0
    a2.x
  } ensuring(res => a1.x + a2.x == res && a2.x == old(a1).x)

}
