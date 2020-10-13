open Collections
open Timbuk
open TimbukTyping

module Symbol : AppSymbol.S with type Base.t = StringSymbol.t
module Base = UserState
module MonoType : MonoType.S with type t = Base.t GenericTypes.mono
module PolyType : PolyType.S with type t = Base.t GenericTypes.poly and type var = int and type mono = MonoType.t
module State = PolyType

module Term : Term.S with type Sym.t = Symbol.t
module Label = NoLabel

module Pattern : Pattern.S with type Sym.t = Symbol.t and type Var.t = Var.t
module Aut : Automaton.S with type Sym.t = Symbol.t and type State.t = State.t and type Label.t = Label.t and type data = unit

module LocPattern : TypedPattern.S with type Sym.t = Symbol.t and type Var.t = Var.t and type Type.t = (State.t option * Codemap.Span.t)
module LocPatternSet : Set.S with type elt = LocPattern.t * Aut.StateSet.t option
module LocRule : Rule.S with type elt = LocPattern.t
module LocTrs : Relation.S with type ord = LocPattern.t and type elt = LocRule.t

module Rule : Rule.S with type elt = Pattern.t
module Trs : Relation.S with type ord = Pattern.t and type elt = Rule.t

module Id : Set.OrderedType with type t = string

module PatternSet : sig
  type t = LocPatternSet.t * Aut.t option
end

module Alphabet : module type of Alphabet.Make (Id) (Symbol)

(** Sets of variables.
    Since we don't want duplicates, the module Dictionary is used. *)
module Variables : sig
  include module type of Dictionary.Make (Id) (Var)

  val print : t -> Format.formatter -> unit
end

module Trss : sig
  include module type of Dictionary.Make (Id) (LocTrs)

  val print : t -> Format.formatter -> unit
end

module Automata : sig
  include module type of Dictionary.Make (Id) (Aut)

  val print : t -> Format.formatter -> unit
end

module PatternSets : sig
  include module type of Dictionary.Make (Id) (PatternSet)

  val print : t -> Format.formatter -> unit
end

(** A timbuk file specification. *)
type t = {
  spec_alphabet : Alphabet.t;
  spec_variables : Variables.t;
  spec_trss : Trss.t;
  spec_automata : Automata.t;
  spec_pattern_sets : PatternSets.t;
}

val state_of_string : string -> State.t

(** Pretty-print a Timbuk file specification. *)
val print : t -> Format.formatter -> unit
