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

module Mono (Base: Automaton.STATE) = struct
  module Base = Base

  type t = Base.t mono

  let rec of_poly = function
    | PolyBase t -> Base t
    | PolyFun (a, b) -> Fun (of_poly a, of_poly b)
    | _ -> raise (Invalid_argument "type is polymorphic")

  let rec compare a b =
    match a, b with
    | Base a, Base b -> Base.compare a b
    | Base _, _ -> 1
    | Fun (a1, a2), Fun (b1, b2) ->
      let c = compare a1 b1 in
      if c = 0 then compare a2 b2 else c
    | Fun _, Base _ -> -1

  let rec equal a b =
    match a, b with
    | Base a, Base b -> Base.equal a b
    | Fun (a1, a2), Fun (b1, b2) -> equal a1 b1 && equal a2 b2
    | _ -> false

  let rec product a b =
    if equal a b then Some a else None

  let hash = Hashtbl.hash

  let rec print t fmt =
    match t with
    | Base b -> Base.print b fmt
    | Fun (Fun (a1, a2), b) ->
      Format.fprintf fmt "(%t) ~> %t" (print (Fun (a1, a2))) (print b)
    | Fun (a, b) ->
      Format.fprintf fmt "%t ~> %t" (print a) (print b)
end

module Poly (Base: Automaton.STATE) = struct
  module Base = Base

  type t = Base.t poly

  let rec compare a b =
    match a, b with
    | PolyVar a, PolyVar b -> a - b
    | PolyVar _, _ -> 1
    | Polymorphic a, Polymorphic b -> a - b
    | Polymorphic _, PolyVar _ -> -1
    | Polymorphic _, _ -> 1
    | PolyBase a, PolyBase b -> Base.compare a b
    | PolyBase _, PolyVar _ -> -1
    | PolyBase _, Polymorphic _ -> -1
    | PolyBase _, _ -> 1
    | PolyFun (a1, a2), PolyFun (b1, b2) ->
      let c = compare a1 b1 in
      if c = 0 then compare a2 b2 else c
    | PolyFun _, PolyVar _ -> -1
    | PolyFun _, Polymorphic _ -> -1
    | PolyFun _, PolyBase _ -> -1

  let rec equal a b =
    match a, b with
    | PolyVar a, PolyVar b -> a = b
    | Polymorphic a, Polymorphic b -> a = b
    | PolyBase a, PolyBase b -> Base.equal a b
    | PolyFun (a1, a2), PolyFun (b1, b2) -> equal a1 b1 && equal a2 b2
    | _ -> false

  let rec product a b =
    if equal a b then Some a else None

  let hash = Hashtbl.hash

  let rec print t fmt =
    match t with
    | PolyVar i -> Format.fprintf fmt "#%d" i
    | Polymorphic i ->
      if i < 26 then
        Format.fprintf fmt "'%c" (Char.chr (0x61 + i))
      else
        Format.fprintf fmt "'%d" (i - 26)
    | PolyBase b -> Base.print b fmt
    | PolyFun (PolyFun (a1, a2), b) ->
      Format.fprintf fmt "(%t) ~> %t" (print (PolyFun (a1, a2))) (print b)
    | PolyFun (a, b) ->
      Format.fprintf fmt "%t ~> %t" (print a) (print b)
end
