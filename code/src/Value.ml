open MyStdLib

type t_node =
  | Func of Param.t * Expr.t
  | Ctor of Id.t * t
  | Tuple of t list
and t = t_node hash_consed
[@@deriving eq, hash, ord, show]

let table = HashConsTable.create 1000

let create
    (node:t_node)
  : t =
  HashConsTable.hashcons
    hash_t_node
    compare_t_node
    table
    node

let node
    (v:t)
  : t_node =
  v.node

let mk_func (a:Param.t) (e:Expr.t) : t =
  create (Func (a,e))

let apply_func (type a) ~(f:Param.t -> Expr.t -> a) (v:t) : a option =
  begin match (node v) with
    | Func (a,e2) -> Some (f a e2)
    | _ -> None
  end

let destruct_func : t -> (Param.t * Expr.t) option =
  apply_func ~f:(fun a e2 -> (a,e2))

let destruct_func_exn (v:t) : Param.t * Expr.t =
  Option.value_exn (destruct_func v)

let mk_ctor (i:Id.t) (v:t) : t =
  create (Ctor (i,v))

let apply_ctor (type a) ~(f:Id.t -> t -> a) (v:t) : a option =
  match node v with
    | Ctor (i,v) -> Some (f i v)
    | _ -> None

let destruct_ctor : t -> (Id.t * t) option =
  apply_ctor ~f:(fun i v -> (i,v))

let destruct_ctor_exn (v:t) : Id.t * t =
  begin match (destruct_ctor v) with
    | Some v -> v
    | None -> failwith (show v)
  end

let mk_tuple (vs:t list) : t =
  begin match vs with
    | [v] -> v
    | _ -> create (Tuple vs)
  end

let apply_tuple (type a) ~(f:t list -> a) (v:t) : a option =
  begin match node v with
    | Tuple vs -> Some (f vs)
    | _ -> None
  end

let destruct_tuple : t -> t list option =
  apply_tuple ~f:ident

let destruct_tuple_exn (v:t) : t list =
  Option.value_exn (destruct_tuple v)

let mk_true : t = mk_ctor (Id.create "True") (mk_tuple [])

let mk_false : t = mk_ctor (Id.create "False") (mk_tuple [])

let rec fold ~(func_f:Param.t -> Expr.t -> 'a)
             ~(ctor_f:Id.t -> 'a -> 'a)
             ~(tuple_f:'a list -> 'a)
            (v:t)
            : 'a =
  let fold_simple = fold ~func_f ~ctor_f ~tuple_f
   in match node v with
        | Func (a,e) -> func_f a e
        | Ctor (i,v) -> ctor_f i (fold_simple v)
        | Tuple vs -> tuple_f (List.map ~f:fold_simple vs)

let to_exp : t -> Expr.t =
  fold ~func_f:Expr.mk_func
       ~ctor_f:Expr.mk_ctor
       ~tuple_f:Expr.mk_tuple

let rec from_exp (e:Expr.t) : t option =
  match Expr.node e with
    | Func (a,e)
      -> Some (mk_func a e)
    | Ctor (i,e)
      -> Option.map ~f:(mk_ctor i) (from_exp e)
    | Tuple es
      -> Option.map ~f:mk_tuple (Some (List.filter_map es ~f:from_exp))
    | Var _
    | App _
    | Proj _
    | Match _
    | Fix _
      -> None

let from_exp_exn (e:Expr.t) : t =
  Option.value_exn (from_exp e)

let rec subvalues (v:t) : t list =
  v :: begin match node v with
         | Func _ -> []
         | Ctor (_,v) -> subvalues v
         | Tuple vs -> List.concat_map ~f:subvalues vs
  end

let strict_subvalues (e:t) : t list =
  List.tl_exn (subvalues e)

let strict_subvalue (e1:t) (e2:t) : bool =
  List.mem ~equal (strict_subvalues e2) e1


let size : t -> int =
  fold
    ~func_f:(fun (_,t) e -> 1 + (Type.size t) + (Expr.size e))
    ~ctor_f:(fun _ i -> i+1)
    ~tuple_f:(fun is -> List.fold ~f:(+) ~init:1 is)

let unit_ = create (Tuple [])
let true_ = create (Ctor (Id.create "True",unit_))
let false_ = create (Ctor (Id.create "False",unit_))
let rec num_val n =
  if n = 0 then
    create (Ctor (Id.create "O",unit_))
  else
    create (Ctor (Id.create "S",num_val (n-1)))
