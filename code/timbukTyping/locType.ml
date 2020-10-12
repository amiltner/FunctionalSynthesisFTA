open Timbuk

module Make (Location : sig type t end) (Type : Automaton.STATE) = struct
  type t = Type.t * Location.t

  let compare (a, _) (b, _) = Type.compare a b

  let equal (a, _) (b, _) = Type.equal a b

  let product (a, span) (b, _) =
    match Type.product a b with
    | Some t -> Some (t, span)
    | None -> None

  let hash (t, _) = Type.hash t

  let print (t, _) fmt = Type.print t fmt
end
