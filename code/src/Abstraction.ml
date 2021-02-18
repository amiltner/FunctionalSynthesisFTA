open MyStdLib
open Lang

module TypedAbs =
struct
  type t = Predicate.t list
  [@@deriving eq, hash, ord, show]

  let abstract
      (a:t)
      (v:Value.t)
    : Predicate.t =
    Predicate.
      (let applies = List.filter ~f:(fun p -> (v => p)) a in
       fold_on_head_exn
         ~f:conjunct_exn
         applies)
end

module D = DictOf(Type)(TypedAbs)

type t = D.t
[@@deriving eq, hash, ord, show]

let add
    (a:t)
    (t:Type.t)
    (p:Predicate.t)
  : t =
  let ps =
    begin match D.lookup a t with
      | None -> [Predicate.top]
      | Some ps -> ps
    end
  in
  D.insert a t (List.dedup_and_sort ~compare:Predicate.compare (p::ps))

let abstract
    (a:t)
    (v:Value.t)
    (t:Type.t)
  : Predicate.t =
  let ta =
    D.lookup_default
      ~default:([Predicate.top])
      a
      t
  in
  TypedAbs.abstract ta v

let abstract_final
    ~(out:Value.t)
    ~(pred:Predicate.t -> bool)
  : Predicate.t =
  out (*TODO*)

let init = D.empty
