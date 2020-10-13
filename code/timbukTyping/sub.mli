open Timbuk

module type S = sig
  module Location : sig type t end

  (** Automaton storing the type system. *)
  module Aut : Automaton.S

  (** Typed pattern. *)
  module TypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = Aut.State.t * Location.t

  (** Optionaly typed TRS. *)
  module TypedTrs : Relation.S with type ord = TypedPattern.t

  (** Possible type errors. *)
  type error =
    | Ambiguity
    | UnificationFailed of Aut.StateSet.t

  (** Typing error. *)
  exception Error of error * Location.t

  (** Typing context, containing the current abstraction. *)
  type t

  val create : Aut.t -> TypedTrs.t -> t

  val type_system : t -> Aut.t

  val typed_trs : t -> TypedTrs.t

  val type_pattern : TypedPattern.t -> t -> TypedPattern.t list * t

  val print_error : error -> Format.formatter -> unit

  val error_label : error -> string option

  (* val format_error_hints : error -> CodeMap.Formatter.t -> unit *)
end

module Make
    (Location : sig type t end)
    (Aut : Automaton.S)
    (TypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = Aut.State.t * Location.t)
    (TypedTrs : Relation.S with type ord = TypedPattern.t)
  : S with module Location = Location
       and module Aut = Aut
       and module TypedPattern = TypedPattern
       and module TypedTrs = TypedTrs
