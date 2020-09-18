open MyStdLib

type t =
  Id.t * Type.t
[@@deriving eq, hash, ord, show]
