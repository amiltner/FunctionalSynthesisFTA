open MyStdLib

module type IdGenerator =
sig
  val fresh : unit -> Id.t
end

module Make(D:Data)(IDG:IdGenerator) =
struct
  module D =
  struct
    include D
    let sexp_of_t _ = failwith "ah"
  end
  module DToID = DictOf(D)(Id)
  module IDToD = DictOf(Id)(D)

  let dd = Hashtbl.create (module D)
  let idd = Hashtbl.create (module Id)

  let get_id
      (d:D.t)
    : Id.t =
    let ido =
      Hashtbl.find
        dd
        d
    in
    begin match ido with
      | None ->
        let id = IDG.fresh () in
        Hashtbl.set
          ~key:d
          ~data:id
          dd;
        Hashtbl.set
          ~key:id
          ~data:d
          idd;
        id
      | Some id -> id
    end

  let get_d
      (id:Id.t)
    : D.t =
    Hashtbl.find_exn
      idd
      id
end
