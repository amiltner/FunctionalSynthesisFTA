open MyStdLib
open Lang

module PartialFunction = struct
  type t = (Value.t * Value.t) list
  [@@deriving eq, hash, ord, show]

  let implies
      (insout1:t)
      (insout2:t)
    : bool =
    sub_multi_set
      ~cmp:(pair_compare Value.compare Value.compare)
      insout2
      insout1
end

module NonpermittedElt = struct
  type t = FTAConstructor.State.t * FTAConstructor.State.t
  [@@deriving eq, hash, ord, show]

  let implies
      (((vals1in,_),(vals1out,_)):t)
      (((vals2in,_),(vals2out,_)):t)
    : bool =
    let to_inout valsin valsout =
      List.map2_exn
        ~f:(fun (dom,inv) (dom',outv) ->
            assert (Value.equal dom dom');
            (dom,inv,outv))
        valsin
        valsout
    in
    let vals1inout = to_inout vals1in vals1out in
    let vals2inout = to_inout vals2in vals2out in
    let valopt_compare = compare_option Value.compare in
    sub_multi_set
      ~cmp:(triple_compare Value.compare valopt_compare valopt_compare)
      vals2inout
      vals1inout
end

module Nonpermitted = struct
  type t = (FTAConstructor.State.t * FTAConstructor.State.t) list
  [@@deriving eq, hash, ord, show]

  let implies
      (npes1:t)
      (npes2:t)
    : bool =
    List.for_all
      ~f:(fun npe2 ->
          List.exists
            ~f:(fun npe1 -> NonpermittedElt.implies npe1 npe2)
            npes1)
      npes2
end

module NPPFConj = struct
  type t = Nonpermitted.t * PartialFunction.t
  [@@deriving eq, hash, ord, show]

  let implies
      ((np1,pf1):t)
      ((np2,pf2):t)
    : bool =
    (PartialFunction.implies pf1 pf2) && (Nonpermitted.implies np1 np2)
end

module Falsified = struct
  type t = NPPFConj.t
  [@@deriving eq, hash, ord, show]

  let falsifies
      (c1:t)
      (c2:t)
    : bool =
    NPPFConj.implies c2 c1
end

type t = Falsified.t list
[@@deriving eq, hash, ord, show]

let empty = []

let add kb f = f::kb

let falsifies
    (kb:t)
    (c:NPPFConj.t)
  : bool =
  List.exists ~f:(fun c' -> Falsified.falsifies c' c) kb
