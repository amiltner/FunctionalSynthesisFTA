open Timbuk

type ('a, 'x) t =
  | Poly of 'x
  | Base of 'a
  | Fun of 'a * 'a

type ('a, 'x) poly = ('a, 'x) t

(** Polymorphic types. *)
module type S = sig
  include Automaton.STATE

  (** Type of type variables. *)
  type var

  (** Monomorphic variant. *)
  type mono

  (** Destruct a polymorphic type into a `PolyType` known by Timbuk. *)
  val destruct : t -> (t, var) poly

  (** Get the monomorphic version of this type.
      Raise an exception if the given type is polymorphic. *)
  val monomorphic : t -> mono
end
