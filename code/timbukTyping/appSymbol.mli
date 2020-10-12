open Timbuk

type 'a sym =
  | App
  | Sym of 'a

module type S = sig
  module Base : Symbol.S

  include Symbol.S with type t = Base.t sym
end

module Make (Base : Symbol.S) : S with module Base = Base
