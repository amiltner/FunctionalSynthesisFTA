module type S = sig
  val synth : problem:Problem.t -> Expr.t
end
