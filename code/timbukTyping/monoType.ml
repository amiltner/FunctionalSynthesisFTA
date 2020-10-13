open Timbuk

type 'a t =
  | Base of 'a
  | Fun of 'a * 'a

type 'a mono = 'a t

(** Monomorphic types. *)
module type S = sig
  include Automaton.STATE

  (** Construct a monomorphic type from a `MonoType` known by Timbuk. *)
  val construct : t mono -> t

  (** Destruct a monomorphic type into a `MonoType` known by Timbuk. *)
  val destruct : t -> t mono
end
