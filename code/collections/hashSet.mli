module type S = sig
  type key
  type t
  val create : int -> t
  val add : key -> t -> t
  val size : t -> int
  val is_empty : t -> bool
  val contains : key -> t -> bool
  val fold : ('b -> key -> 'b) -> 'b -> t -> 'b
  val as_list : t -> key list
  val iter : (key -> unit) -> t -> unit
  val union : t -> t -> t
  val pp : (Format.formatter -> key -> unit) -> Format.formatter -> t -> unit
end

module Make (K: HashTable.HashedType) : S with type key = K.t
