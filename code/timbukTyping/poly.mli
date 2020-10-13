open Timbuk

module type S = sig
  module Location : sig type t end

  module Sym : AppSymbol.S

  module Base : Automaton.STATE

  (** Automaton storing the type system. *)
  module Aut : Automaton.S with type Sym.t = Sym.t and type State.t = Base.t GenericTypes.poly and type Label.t = unit

  (** Optionaly typed patterns. *)
  module OptTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Base.t GenericTypes.poly option * Location.t)

  (** Optionaly typed TRS. *)
  module Trs : Relation.S with type ord = OptTypedPattern.t

  (** Typed pattern (spans are dropped). *)
  module TypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Var.t = OptTypedPattern.Var.t and type Type.t = Base.t GenericTypes.poly * Location.t

  (** Typed TRS. *)
  module TypedTrs : Relation.S with type ord = TypedPattern.t

  (** Possible type errors. *)
  type error =
    | NonLinearLHS
    | NonNormalizedTypeAut
    | NotFunctional
    | TypeMissmatch of Aut.State.t * Location.t option * Aut.State.t
    | PatternSubtyping of Base.t GenericTypes.poly * Base.t GenericTypes.poly
    | InvalidCast of Base.t GenericTypes.poly * TypedPattern.t
    | InvalidArity of Aut.Sym.t * int * int

  (** Typing error. *)
  exception Error of error * Location.t

  (** Typing context, containing the current abstraction. *)
  type t

  val create : Trs.t -> Aut.t -> t

  val type_system : t -> Aut.t

  val typed_trs : t -> TypedTrs.t

  val type_pattern : OptTypedPattern.t -> t -> TypedPattern.t * t

  val print_error : error -> Format.formatter -> unit

  val error_label : error -> string option

  (* val format_error_hints : error -> Location.Formatter.t -> unit *)
end

module Make
    (Location : sig type t end)
    (Sym : AppSymbol.S)
    (Base : Automaton.STATE)
    (Aut : Automaton.S with type Sym.t = Sym.t and type State.t = Base.t GenericTypes.poly and type Label.t = unit)
    (OptTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Base.t GenericTypes.poly option * Location.t))
    (Trs : Relation.S with type ord = OptTypedPattern.t)
    (TypedTrs : Relation.S with type ord = (Sym.t, OptTypedPattern.Var.t, Base.t GenericTypes.poly * Location.t) TypedPattern.typed_pattern)
  : S with module Location = Location
       and module Sym = Sym
       and module Base = Base
       and module Aut = Aut
       and module OptTypedPattern = OptTypedPattern
       and module Trs = Trs
       and module TypedTrs = TypedTrs
