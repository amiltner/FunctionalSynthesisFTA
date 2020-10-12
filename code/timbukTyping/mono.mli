open Timbuk

module type S = sig
  module Location : sig type t end

  (** Functional sympols. *)
  module Sym : AppSymbol.S

  (** Monomorphic type. *)
  module Mono : MonoType.S

  (** Polymorphic type to monomorphize. *)
  module Poly : PolyType.S with type mono = Mono.t

  (** Automaton storing the polymorphic type system. *)
  module PolyAut : Automaton.S with type Sym.t = Sym.t and type State.t = Poly.t

  (** Polymorphic pattern. *)
  module PolyTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Poly.t * Location.t)

  (** Polymorphic TRS. *)
  module PolyTypedTrs : Relation.S with type ord = PolyTypedPattern.t

  (** Monomorphic type system. *)
  module MonoAut : Automaton.S with type Sym.t = Sym.t * Mono.t list * Mono.t and type State.t = Mono.t and type Label.t = PolyAut.Label.t

  (** Typed pattern (spans are dropped). *)
  module MonoTypedPattern : TypedPattern.S with type Sym.t = MonoAut.Sym.t and type Var.t = PolyTypedPattern.Var.t and type Type.t = (Mono.t * Location.t)

  (** Typed TRS. *)
  module MonoTypedTrs : Relation.S with type ord = MonoTypedPattern.t

  (** Possible type errors. *)
  type error =
    | PolymorphicType of Poly.t

  (** Typing error. *)
  exception Error of error * Location.t

  (** Typing context, containing the current abstraction. *)
  type t

  val create : ?constant_refiner:(MonoAut.Configuration.t -> (MonoAut.State.t * MonoAut.Label.t * MonoAut.Label.t)) -> PolyTypedTrs.t -> PolyAut.t -> t

  val type_system : t -> MonoAut.t

  val typed_trs : t -> MonoTypedTrs.t

  val type_pattern : PolyTypedPattern.t -> t -> MonoTypedPattern.t * t

  val print_error : error -> Format.formatter -> unit

  val error_label : error -> string option

  (* val format_error_hints : error -> Location.Formatter.t -> unit *)
end

module Make
    (Location : sig type t end)
    (Sym : AppSymbol.S)
    (Mono : MonoType.S)
    (Poly : PolyType.S with type mono = Mono.t)
    (PolyAut : Automaton.S with type Sym.t = Sym.t and type State.t = Poly.t)
    (PolyTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Poly.t * Location.t))
    (PolyTypedTrs : Relation.S with type ord = PolyTypedPattern.t)
    (MonoAut : Automaton.S with type Sym.t = Sym.t * Mono.t list * Mono.t and type State.t = Mono.t and type data = unit and type Label.t = PolyAut.Label.t)
    (MonoTypedPattern : TypedPattern.S with type Sym.t = MonoAut.Sym.t and type Var.t = PolyTypedPattern.Var.t and type Type.t = (Mono.t * Location.t))
    (MonoTypedTrs : Relation.S with type ord = MonoTypedPattern.t)
  : S with module Location = Location
       and module Sym = Sym
       and module Mono = Mono
       and module Poly = Poly
       and module PolyAut = PolyAut
       and module PolyTypedPattern = PolyTypedPattern
       and module PolyTypedTrs = PolyTypedTrs
       and module MonoAut = MonoAut
       and module MonoTypedPattern = MonoTypedPattern
       and module MonoTypedTrs = MonoTypedTrs
