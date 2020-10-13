open Timbuk

type 'a sym =
  | App
  | Sym of 'a

module type S = sig
  module Base : Symbol.S

  include Symbol.S with type t = Base.t sym
end

module Make (Base : Symbol.S) = struct
  module Base = Base

  type t = Base.t sym

  let compare a b =
    match a, b with
    | App, App -> 0
    | App, _ -> 1
    | Sym a, Sym b -> Base.compare a b
    | Sym _, _ -> -1

  let equal a b =
    match a, b with
    | App, App -> true
    | Sym a, Sym b -> Base.equal a b
    | _ -> false

  let hash = function
    | App -> 0
    | Sym f -> Base.hash f

  let print f fmt =
    match f with
    | App -> Format.fprintf fmt "@@"
    | Sym f -> Base.print f fmt

  let arity = function
    | App -> 2
    | Sym f -> Base.arity f
end
