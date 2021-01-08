module type S = sig
  type elt
  type t
  val create : int -> t
  val empty : unit -> t
  val add : elt -> t -> t
  val size : t -> int
  val is_empty : t -> bool
  val contains : elt -> t -> bool
  val fold : ('b -> elt -> 'b) -> 'b -> t -> 'b
  val as_list : t -> elt list
  val iter : (elt -> unit) -> t -> unit
  val union : t -> t -> t
  val pp : (Format.formatter -> elt -> unit) -> Format.formatter -> t -> unit
end

module Make (K: HashTable.HashedType) = struct
  module D = HashTable.Make(K)
  type elt = K.t
  type t = bool D.t

  let create = D.create

  let empty _ = create 1000

  let add k s = D.set k true s

  let size = D.size

  let is_empty = D.is_empty

  let contains k s =
    begin match D.find_opt k s with
      | None -> false
      | Some b -> b
    end

  let fold f init s =
    D.fold
      (fun acc k b ->
         if b then
           f acc k
         else
           acc)
      init
      s

  let as_list =
    fold
      (fun acc h -> h::acc)
      []

  let iter f s =
    D.iter
      (fun k b ->
         if b then
           f k
         else
           ())
      s

  let union s1 s2 =
    D.union
      (fun k b1 b2 ->
         if b1 || b2 then
           Some true
         else
           None)
      s1
      s2

  let pp k_pp f s =
    Format.fprintf
      f
      "[";
    iter
      (fun k -> k_pp f k)
      s;
    Format.fprintf
      f
      "]";
end
