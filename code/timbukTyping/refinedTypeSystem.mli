open Collections
open Timbuk

module type S = sig
  (* module Type : Automaton.STATE *)
  (** The type module. In our case, a type is just a state recognizing a
      language of values (irreducible terms).
      In the [refined_knowledge_automaton], states recnognize also non-value
      terms, as long as they rewrite into a value of the same state.
      Finaly, we do the distinction between "simple types" and "refined types".
      Simple types are those of the classical type system (int, bool, list,
      etc.), and refined types recognize (non-strict-)subsets of simple types.
      A simple type is also a refined type. *)

  module TypeAut : Automaton.S with type Label.t = unit and type data = unit
  (** A type automaton, defining types. Type automata are always complete,
      "locally" deterministic and "locally" normalized.
      The "locally" here means that it is try when considering refined types
      living in the same partition of simple types. *)

  module TypeSet : Set.S with type t = TypeAut.StateSet.t and type elt = TypeAut.StateSet.elt

  module TypeSetSet : Set.S with type elt = TypeSet.t

  type t

  val create : TypeAut.t -> TypeAut.t -> (unit -> TypeAut.State.t) -> t
  (** [create simple_types refined_types] create a new type system with the
      given refinement.
      Note that any refined partition in [refined_types] must be declared
      afterward using [declare_partition]. *)

  val automaton : t -> TypeAut.t
  (** [automaton t] get the automaton recognizing the simple types. *)

  val refined_automaton : t -> TypeAut.t
  (** [refined_automaton t] returns the automaton of refined typed values. *)

  val refined_knowledge_automaton : t -> TypeAut.t
  (** [refined_knowledge_automaton t] returns the automaton of refined typed
      values and functions. *)

  val update : TypeAut.t -> TypeAut.t -> t -> t
  (** [update refined_automaton refined_knowledge_automaton t] update with
      the given [refined_automaton] and [refined_knowledge_automaton]. The input
      automata must include syntactically the previous ones (types do not change
      after an update). *)

  (* val simple_types_of_refined : t -> TypeAut.State.t -> TypeAut.StateSet.t *)
  (** [simple_type_of_refined t refined_ty] get the simple types of which
      [refined_ty] is a part of. *)

  (* val has_simple_type : t -> TypeAut.State.t -> TypeAut.State.t -> bool *)
  (* [has_simple_type t simple_ty refined_ty] checks if [refined_ty] has
     [simple_ty] as simple type. *)

  val complements_of : t -> TypeAut.State.t -> TypeSetSet.t
  (** [complement_of t refined_ty] return the set of set of known regular
      types for which the union with [regular_ty] is forming the partition of a
      simple type. *)

  val declare_partition : TypeAut.State.t -> TypeSet.t -> t -> t
  (** [declare_partition simple_ty set t] declare [set] as partition of the
      simple type [ty]. [set] must indeed be a partition of [ty] (it is not
      checked). *)

  val declare_subtype : TypeAut.State.t -> TypeAut.State.t -> t -> t
  (** [declare_subtype a b t] declares that [b] is a subtype of [a]. *)

  val is_subtype : t -> TypeAut.State.t -> TypeAut.State.t -> bool
  (** [is_subtype t a b] checks if the type [b] is a subtype of the
      type [a]. *)

  val is_direct_subtype : t -> TypeAut.State.t -> TypeAut.State.t -> bool
  (** [is_subtype t a b] checks if the type [b] is a direct subtype of the
      type [a]. *)

  val most_precise_type : t -> TypeAut.State.t -> TypeAut.State.t -> TypeAut.State.t
  (** [most_precise_type t a b] return the most precise type between [a]
      and [b]. Raise an error if types are incompatibles. *)

  val subtype_partition : t -> TypeSet.t * TypeAut.State.t -> TypeAut.State.t -> (TypeAut.State.t -> TypeAut.State.t option) * t
  (** [subtype_partition t (partition, simple_ty) sub_ty] return a mapping
      between elements of the [partition] of [simple_ty] to elemnts of the same
      partition of [sub_ty].
      Since the target type is a sub-type of [simple_ty], some elements may not
      be mapped to anything.
      A new [t] is also returned since the computation of the refined partition
      is done on demand. *)

  type type_product = TypeAut.State.t * TypeAut.State.t -> TypeAut.State.t

  val partition_intersection : TypeAut.State.t -> TypeSet.t -> TypeSet.t -> t -> type_product * (TypeAut.State.t * TypeAut.State.t) list * t
end

module Make (TypeAut : Automaton.S with type Label.t = unit and type data = unit) : sig
  include S with module TypeAut = TypeAut
end
