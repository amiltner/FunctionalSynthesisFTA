open Timbuk

module Make (Location : sig type t end) (Type : Automaton.STATE) :
  Automaton.STATE with type t = Type.t * Location.t
