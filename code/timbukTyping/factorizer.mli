open Collections
open Timbuk
open TimbukSolving

module type S = sig
  module Aut : Automaton.S
  module Partition : Set.S with type elt = Aut.StateSet.t

  val factorize : (Aut.Sym.t * Aut.State.t list * Aut.State.t) -> Partition.t -> (Aut.State.t -> Aut.State.t -> bool) -> Aut.t -> (Partition.t list) option
end

module Make (Aut : Automaton.S) (P : Set.S with type elt = Aut.StateSet.t) (Solver : Solver.S with type Var.t = Aut.State.t) : sig
  include S with module Aut = Aut
             and module Partition = P
end
