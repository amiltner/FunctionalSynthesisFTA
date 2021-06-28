package pp

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._

/**
 * An instance of a packrat parser that uses the Expressions grammar presented in Bryan Ford ICFP 
 * 2002 paper "Simple, powerful, lazy, linear time, functional pearl".
 * The implementation is almost exactly as the memoized implementation that was presented in the paper, 
 * but here indices are passed around between parse functions, instead of strings.
 * The input list of tokens is represented as an array of tokens which can be looked up based on an index
 * in constant time and zero memory usage (and so is marked as @exten).
 */
object PackratParsing {

  sealed abstract class Terminal
  case class Open() extends Terminal
  case class Close() extends Terminal
  case class Plus() extends Terminal
  case class Times() extends Terminal
  case class Digit() extends Terminal

  /**
   * A mutable array of tokens returned by the lexer.
   * The string of tokens is reversed i.e,
   * string(legnth-1) represents the first char and string(0) represents the last char.
   */
  @ignore
  var string = Array[Terminal]()

  /**
   * looking up the ith token
   */
  @extern
  def lookup(i: BigInt): Terminal = {
    string(i.toInt)
  } ensuring (_ => alloc <= 0)

  sealed abstract class Result {
    /**
     * Checks if the index in the result (if any) is
     * smaller than `i`
     */
    @inline
    def smallerIndex(i: BigInt) = this match {
      case Parsed(m) => m < i
      case _         => true
    }
  }
  case class Parsed(rest: BigInt) extends Result
  case class NoParse() extends Result

  @invisibleBody
  @memoize
  @invstate
  def pAdd(i: BigInt): Result = {
    require {
      if (depsEval(i) && cached(pMul(i)) && cached(pPrim(i)))
        resEval(i, pMul(i)) // lemma inst
      else false
    }
    // Rule 1: Add <- Mul + Add
    val mulRes = pMul(i)
    mulRes match {
      case Parsed(j) =>
        if (j > 0 && lookup(j) == Plus()) {
          pAdd(j - 1) match {
            case Parsed(rem) =>
              Parsed(rem)
            case _ =>
              mulRes // Rule2: Add <- Mul
          }
        } else mulRes
      case _ =>
        mulRes
    }
  } ensuring (res => res.smallerIndex(i) && alloc <= ?) 

  @invisibleBody
  @memoize
  @invstate
  def pMul(i: BigInt): Result = {
    require{
      if (depsEval(i) && cached(pPrim(i)))
        resEval(i, pPrim(i)) // lemma inst
      else false
    }
    // Rule 1: Mul <- Prim *  Mul
    val primRes = pPrim(i)
    primRes match {
      case Parsed(j) =>
        if (j > 0 && lookup(j) == Times()) {
          pMul(j - 1) match {
            case Parsed(rem) =>
              Parsed(rem)
            case _ =>
              primRes // Rule2: Mul <- Prim
          }
        } else primRes
      case _ =>
        primRes
    }
  } ensuring (res => res.smallerIndex(i) && alloc <= ?) 

  @invisibleBody
  @memoize
  @invstate
  def pPrim(i: BigInt): Result = {
    require(depsEval(i))
    val char = lookup(i)
    if (char == Digit()) {
      if (i > 0)
        Parsed(i - 1) // Rule1: Prim <- Digit
      else
        Parsed(-1) // here, we can use -1 to convey that the suffix is empty
    } else if (char == Open() && i > 0) {
      pAdd(i - 1) match { // Rule 2: pPrim <- ( Add )
        case Parsed(rem) =>
          if (rem >= 0 && lookup(rem) == Close()) Parsed(rem - 1)
          else NoParse()
        case _ =>
          NoParse()
      }
    } else NoParse()
  } ensuring (res => res.smallerIndex(i) && alloc <= ?) 

  def depsEval(i: BigInt) =
    if (i == 0) true
    else if (i > 0) allEval(i - 1)
    else false

  def allEval(i: BigInt): Boolean = {
    require(i >= 0)
    (cached(pPrim(i)) && cached(pMul(i)) && cached(pAdd(i))) && (
      if (i == 0) true
      else allEval(i - 1))
  }

  @traceInduct
  def evalMono(i: BigInt, st1: Set[Fun[Result]], st2: Set[Fun[Result]]) = {
    require(i >= 0)
    (st1.subsetOf(st2) && (allEval(i) in st1)) ==> (allEval(i) in st2)
  } holds

  @traceInduct
  def depsLem(x: BigInt, y: BigInt) = {
    require(x >= 0 && y >= 0)
    (x <= y && allEval(y)) ==> allEval(x)
  } holds

  /**
   * Instantiates the lemma `depsLem` on the result index (if any)
   */
  def resEval(i: BigInt, res: Result) = {
    (res match {
      case Parsed(j) =>
        if (j >= 0 && i > 1) depsLem(j, i - 1)
        else true
      case _ => true
    })
  }

  def invokePrim(i: BigInt): Result = {
    require(depsEval(i))
    pPrim(i)
  } ensuring { res =>
    {val in = inSt[Result]
    val out = outSt[Result]
    (if (i > 0) evalMono(i - 1, in, out) else true)} &&
    alloc <= ?
  }

  def invokeMul(i: BigInt): Result = {
    require(depsEval(i))
    invokePrim(i) match {
      case _ => pMul(i)
    }
  } ensuring { res =>
    {val in = inSt[Result]
    val out = outSt[Result]
    (if (i > 0) evalMono(i - 1, in, out) else true)} &&
    alloc <= ?
  }

  def invoke(i: BigInt): Result = {
    require(depsEval(i))
    invokeMul(i) match {
      case _ => pAdd(i)
    }
  } ensuring { res =>
    val in = inSt[Result]
    val out = outSt[Result]
    (if (i > 0) evalMono(i - 1, in, out) else true) &&
      allEval(i) &&
      alloc <= ? 
  }

  /**
   * Parsing a string of length 'n+1'.
   * Word is represented as an array indexed by 'n'. We only pass around the index.
   */
  def parse(n: BigInt): Result = {
    require(n >= 0)
    if (n == 0) invoke(n)
    else {
      parse(n - 1) match { // we parse the prefixes ending at 0, 1, 2, 3, ..., n
        case _ =>
          invoke(n)
      }
    }
  } ensuring (_ => allEval(n) &&
    alloc <= ? * n + ?) 

  @ignore
  def main(args: Array[String]) {
    // list of tokens to parse. The list is reversed i.e, the first char is at the last index, the last char is at the first index.
    string = Array(Plus(), Digit(), Times(), Close(), Digit(), Plus(), Digit(), Open()) // d *  ( d + d ) +
    println("Parsing Expression 1: " + parse(string.length - 1))
  }

}
