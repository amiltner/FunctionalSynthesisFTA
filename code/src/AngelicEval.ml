open MyStdLib
open Lang

type expr =
  | Var of Id.t
  | App of expr * expr
  | Func of Param.t * expr
  | Ctor of Id.t * expr
  | Unctor of Id.t * expr
  | Match of expr * Id.t * (Id.t * expr) list
  | Fix of Id.t * Type.t * expr
  | Tuple of expr list
  | Proj of int * expr
  | AngelicF of expr
  | Wildcard

and value =
  | Func of Param.t * expr
  | Ctor of Id.t * value
  | Tuple of value list
  | Wildcard
[@@deriving eq, show]

let mk_value_ctor (i:Id.t) (v:value) : value = Ctor (i,v)

let from_exp =
  Expr.fold
    ~var_f:(fun i -> Var i)
    ~app_f:(fun e1 e2 -> App (e1,e2))
    ~func_f:(fun p e -> Func(p,e))
    ~ctor_f:(fun i e -> Ctor(i,e))
    ~unctor_f:(fun i e -> Unctor (i,e))
    ~match_f:(fun e i bs -> Match(e,i,bs))
    ~tuple_f:(fun es -> Tuple es)
    ~proj_f:(fun i e -> Proj(i,e))
    ~fix_f:(fun i t e -> Fix (i,t,e))
    ~wildcard_f:(Wildcard)

let from_value : Value.t -> value =
  Value.fold
    ~func_f:(fun p e -> (Func (p,from_exp e) : value))
    ~ctor_f:(fun i e -> Ctor(i,e))
    ~tuple_f:(fun es -> Tuple es)
    ~wildcard_f:(Tuple [])

let rec to_exp
    (e:expr)
  : Expr.t =
  begin match e with
    | Wildcard -> Expr.mk_wildcard
    | Var i -> Expr.mk_var i
    | App (e1,e2) -> Expr.mk_app (to_exp e1) (to_exp e2)
    | Func (p,e) ->
      Expr.mk_func
        p
        (to_exp e)
    | Ctor (i,e) -> Expr.mk_ctor i (to_exp e)
    | Unctor (i,e) -> Expr.mk_unctor i (to_exp e)
    | Match (e,i,matches) ->
      Expr.mk_match
        (to_exp e)
        i
        (List.map ~f:(fun (i,e) -> (i,to_exp e)) matches)
    | Tuple es -> Expr.mk_tuple (List.map ~f:to_exp es)
    | Proj (i,e) -> Expr.mk_proj i (to_exp e)
    | AngelicF e -> failwith "no"
    | Fix (i,t,e) -> Expr.mk_fix i t (to_exp e)
  end

let rec to_value
    (v:value)
  : Value.t =
  begin match v with
    | Func (p,e) ->
      Value.mk_func
        p
        (to_exp e)
    | Ctor (i,e) -> Value.mk_ctor i (to_value e)
    | Tuple es -> Value.mk_tuple (List.map ~f:to_value es)
    | Wildcard -> Value.mk_wildcard
  end


let rec value_to_exp
    (v:value)
  : expr =
  begin match v with
    | Func (p,e) -> Func (p,e)
    | Ctor (i,v) -> Ctor (i,value_to_exp v)
    | Tuple vs -> Tuple (List.map ~f:value_to_exp vs)
    | Wildcard -> Wildcard
  end


let rec replace
    (i:Id.t)
    (e_with:expr)
    (e:expr)
  : expr =
  let replace_simple = replace i e_with in
  begin match e with
    | AngelicF e -> AngelicF (replace_simple e)
    | Var i' ->
      if Id.equal i i' then
        e_with
      else
        e
    | App (e1,e2) ->
      App (replace_simple e1,replace_simple e2)
    | Func ((i',t),e') ->
      if Id.equal i i' then
        e
      else
        Func ((i',t),(replace_simple e'))
    | Ctor (i,e) ->
      Ctor (i,(replace_simple e))
    | Unctor (i,e) ->
      Unctor (i,(replace_simple e))
    | Match (e,i',branches) ->
      let branches =
        if Id.equal i i' then
          branches
        else
          List.map
            ~f:(fun (i,e) -> (i,replace_simple e))
            branches
      in
      Match ((replace_simple e),i',branches)
    | Tuple es ->
      Tuple
        (List.map ~f:replace_simple es)
    | Proj (i,e) ->
      Proj (i,(replace_simple e))
    | Fix (i',t,e') ->
      if Id.equal i i' then
        e
      else
        Fix (i',t,replace_simple e')
    | Wildcard -> Wildcard
  end

let rec evaluate
    (angelics : (value * value) list)
    (e : expr)
  : ((value * value) list * value) =
  let evaluate = evaluate angelics in
  begin match e with
    | AngelicF e ->
      let (vs,inv) = evaluate e in
      let outv = List.Assoc.find_exn ~equal:equal_value angelics inv in
      ((inv , outv)::vs,outv)
    | Var i -> failwith ("unbound variable " ^ (Id.show i))
    | App (e1,e2) ->
      let (vins1,v1) = evaluate e1 in
      let (vins2,v2) = evaluate e2 in
      let vins = vins1@vins2 in
      let e1 = value_to_exp v1 in
      let e2 = value_to_exp v2 in
      begin match e1 with
        | Func ((i,_),e1) ->
          let fulle = replace i e2 e1 in
          let (vinscall,res) = evaluate fulle in
          (vinscall@vins,res)
        | _ -> failwith ("nonfunc applied: " ^ (show_expr e1))
      end
    | Func (a,e) ->
      ([],Func (a,e))
    | Ctor (i,e) ->
      let (vcalls,v) = evaluate e in
      (vcalls,(Ctor (i,v) : value))
    | Fix (i,_,e') ->
      evaluate (replace i e e')
    | Match (e,i,branches) as match_expr ->
      let (vcalls,v) = evaluate e in
      begin match v with
        | Ctor (choice,v) ->
          let branch_o = List.Assoc.find ~equal:Id.equal branches choice in
          let branch =
            begin match branch_o with
              | None ->
                failwith
                  ("constructor "
                   ^ (Id.show choice)
                   ^ " not matched: \n "
                   ^ (show_expr match_expr))
              | Some b -> b
            end
          in
          let (vcalls',v) = evaluate (replace i (value_to_exp v) branch) in
          (vcalls@vcalls',v)
        | Wildcard -> (vcalls,Wildcard)
        | _ -> failwith "no soln"
      end
    | Tuple es ->
      let (vcalls,vs) =
        List.unzip (List.map ~f:evaluate es)
      in
      let allcalls = List.concat vcalls in
      (allcalls,Tuple vs)
    | Proj (i,e) ->
      let (vcalls,v) = evaluate e in
      begin match v with
        | Tuple vs -> (vcalls,List.nth_exn vs i)
        | Wildcard -> (vcalls,Wildcard)
        | _ -> failwith "bad"
      end
    | Unctor (i,e) ->
      let (vcalls,v) = evaluate e in
      begin match v with
        | Ctor (i',e) ->
          assert (Id.equal i  i');
          (vcalls,e)
        | Wildcard -> (vcalls,Wildcard)
        | _ -> failwith "ah"
      end
    | Wildcard -> ([],Wildcard)
  end

let replace_holes
    ~(i_e:(Id.t * expr) list)
    (e:expr)
  : expr =
  List.fold_left
    ~f:(fun acc (i,e) -> replace i e acc)
    ~init:e
    i_e

let evaluate_with_holes
    ~eval_context:(i_e:(Id.t * expr) list)
    (ios:(value * value) list)
    (e:expr)
  : (value * value) list * value =
  let e = replace_holes ~i_e e in
  evaluate ios e
