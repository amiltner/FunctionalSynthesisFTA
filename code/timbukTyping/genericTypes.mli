open Timbuk

type 'a mono =
  | Base of 'a
  | Fun of 'a mono * 'a mono

type 'a poly =
  | PolyVar of int
  | Polymorphic of int
  | PolyBase of 'a
  | PolyFun of 'a poly * 'a poly

module type MONO = sig
  module Base : Automaton.STATE

  include Automaton.STATE with type t = Base.t mono

  val of_poly : Base.t poly -> t
end

module type POLY = sig
  module Base : Automaton.STATE

  include Automaton.STATE with type t = Base.t poly
end

module Mono (Base: Automaton.STATE) :
  MONO with module Base = Base

module Poly (Base: Automaton.STATE) :
  POLY with module Base = Base
