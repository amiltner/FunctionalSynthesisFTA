module type ORDERED_FORMAT_TYPE = Symbol.ORDERED_FORMAT_TYPE

module type VARIABLE = sig
  include ORDERED_FORMAT_TYPE

  val product : t -> t -> t option
  (** Variable internal product. *)
end

type position = Term.position

type ('sym, 'x) pattern =
  | Cons of 'sym * (('sym, 'x) pattern) list
  | Var of 'x

module type S = sig
  module Sym : Symbol.S
  module Var : VARIABLE

  type ('sym, 'x) abs_pattern = ('sym, 'x) pattern =
    | Cons of 'sym * (('sym, 'x) pattern) list
    | Var of 'x

  type term = Sym.t Term.term
  type t = (Sym.t, Var.t) pattern

  exception InvalidPosition of position * t

  val create : Sym.t -> t list -> t

  val of_term : term -> t

  val of_var : Var.t -> t

  val is_cons : t -> bool

  val is_var : t -> bool

  val normalized : t -> Var.t

  val subterm : position -> t -> t

  val subterm_opt : position -> t -> t option

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val hash : t -> int

  (** fold the variables in the term. *)
  val fold : (Var.t -> 'a -> 'a) -> t -> 'a -> 'a

  val is_closed : t -> bool

  val for_all : (Var.t -> bool) -> t -> bool

  val apply : (Var.t -> t) -> t -> t

  val instanciate : (Var.t -> term) -> t -> term

  val as_term : t -> term
  (** Raise Invalid_argument if not a term. *)

  (** Pattern internal product. *)
  val product : t -> t -> t option

  val print : t -> Format.formatter -> unit

  (** Format with a special formatter for variables *)
  val print_var : (Var.t -> Format.formatter -> unit) -> t -> Format.formatter -> unit
end

module Make (F: Symbol.S) (X: VARIABLE) : S with module Sym = F and module Var = X

(** Pattern external operations. *)
module Ext (A : S) (B : S with module Sym = A.Sym) : sig
  val substitute : (A.Var.t -> B.t) -> A.t -> B.t
end

module Product (A : S) (B : S with module Sym = A.Sym) (AB : S with module Sym = B.Sym) : sig
  val product : (A.Var.t -> B.Var.t -> AB.Var.t option) -> A.t -> B.t -> AB.t option
  (** Pattern external product *)
end
