type t = unit

let compare _ _ = 0

let product _ _ = Some ()

let print _ _ = ()

let equal _ _ = true

let hash _ = 0

let hash_fold_t = MyStdLib__.Util.hash_fold_from_hash hash
