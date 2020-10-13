open Timbuk

module type S = sig
  module Location : sig type t end

  (** Automaton storing the type system. *)
  module Aut : Automaton.S

  (** Optionaly typed patterns. *)
  module OptTypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = (Aut.State.t option * Location.t)

  (** Optionaly typed TRS. *)
  module Trs : Relation.S with type ord = OptTypedPattern.t

  (** Typed pattern (spans are dropped). *)
  module TypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Var.t = OptTypedPattern.Var.t and type Type.t = Aut.State.t

  (** Typed TRS. *)
  module TypedTrs : Relation.S with type ord = TypedPattern.t

  (** Possible type errors. *)
  type error =
    | NonLinearLHS
    | NonNormalizedTypeAut
    | Diverging of (Aut.Sym.t * Aut.State.t list)
    | NoRuleMatch of (Aut.Sym.t * Aut.State.t list)
    | InvalidType of Aut.State.t option * Aut.State.t option
    | UnificationFailed of Aut.State.t * Aut.State.t
    | NoType

  (** Typing error. *)
  exception Error of error * Location.t

  (** Typing context, containing the current abstraction. *)
  type t

  type ho_helper = {
    is_application: Aut.Sym.t -> bool;
    make_application: int -> bool
  }

  val create : ?ho:ho_helper -> Trs.t -> Aut.t -> t

  val type_system : t -> Aut.t

  val typed_trs : t -> TypedTrs.t

  val type_pattern : t -> (OptTypedPattern.Var.t -> Aut.State.t option) -> OptTypedPattern.t -> TypedPattern.t * t

  val print_error : error -> Format.formatter -> unit

  val error_label : error -> string option

  (* val format_error_hints : error -> CodeMap.Formatter.t -> unit *)
end

module Make
    (Location : sig type t end)
    (Aut : Automaton.S)
    (OptTypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = (Aut.State.t option * Location.t))
    (Trs : Relation.S with type ord = OptTypedPattern.t)
    (TypedTrs : Relation.S with type ord = (Aut.Sym.t, OptTypedPattern.Var.t, Aut.State.t) TypedPattern.typed_pattern)
  : S with module Location = Location
       and module Aut = Aut
       and module OptTypedPattern = OptTypedPattern
       and module Trs = Trs
       and module TypedTrs = TypedTrs
