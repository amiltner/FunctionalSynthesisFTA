open MyStdLib
open Lang

include DictOf(Value)(Abstraction)

let lookup
    (d:t)
    (k:key)
  : value =
  lookup_default ~default:Abstraction.init d k

let integrate_refinement
    (ad:t)
    (vps:(Value.t * Type.t * Predicate.t) list)
  : t =
  List.fold
    ~f:(fun ad (v,t,p) ->
        let va = lookup ad v in
        let va = Abstraction.add va t p in
        insert ad v va)
    ~init:ad
    vps

let abstract
    (ad:t)
    (vin:Value.t)
    (vout:Value.t)
    (t:Type.t)
  : Predicate.t =
  let abstraction =
    lookup
      ad
      vin
  in
  Abstraction.abstract
    abstraction
    vout
    t
