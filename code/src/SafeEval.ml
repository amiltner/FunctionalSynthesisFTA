open MyStdLib
open Lang

type expr =
  | Var of Id.t
  | Wildcard
  | App of expr * expr
  | Func of Param.t * expr
  | Ctor of Id.t * expr
  | Unctor of Id.t * expr
  | Match of expr * Id.t * (Id.t * expr) list
  | Fix  of Id.t * Type.t * expr
  | Tuple of expr list
  | Proj of int * expr
  | UpdateChecks of (value -> value -> bool) * expr * expr
  | Check of expr

and value =
  | Func of Param.t * expr
  | Ctor of Id.t * value
  | Tuple of value list
  | Wildcard
[@@deriving show]

let from_exp =
  Expr.fold
    ~var_f:(fun i -> Var i)
    ~app_f:(fun e1 e2 -> App (e1,e2))
    ~func_f:(fun p e -> Func(p,e))
    ~ctor_f:(fun i e -> Ctor(i,e))
    ~unctor_f:(fun i e -> Unctor (i,e))
    ~match_f:(fun e i bs -> Match(e,i,bs))
    ~fix_f:(fun i t e -> Fix(i,t,e))
    ~tuple_f:(fun es -> Tuple es)
    ~proj_f:(fun i e -> Proj(i,e))
    ~wildcard_f:(Wildcard)

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
    | UpdateChecks (f,earg,e) -> UpdateChecks (f,replace_simple earg,replace_simple e)
    | Check e -> Check (replace_simple e)
    | Wildcard -> e
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
    | Fix (i',t,e') ->
      if Id.equal i i' then
        e
      else
        Fix (i',t,(replace_simple e'))
    | Tuple es ->
      Tuple
        (List.map ~f:replace_simple es)
    | Proj (i,e) ->
      Proj (i,(replace_simple e))
  end

let rec evaluate
    (current_check : value -> bool)
    (e : expr)
  : value =
  begin match e with
    | UpdateChecks (f,earg,e) ->
      let varg = evaluate current_check earg in
      evaluate (f varg) e
    | Check e ->
      let v = evaluate current_check e in
      if current_check v then
        v
      else
        failwith "broken"
    | Wildcard -> Wildcard
    | Var i -> failwith ("unbound variable " ^ (Id.show i))
    | App (e1,e2) ->
      let (v1) = evaluate current_check e1 in
      let e1 = (value_to_exp v1) in
      begin match e1 with
        | Func ((i,_),e1) ->
          let (v2) = evaluate current_check e2 in
          let e2 = (value_to_exp v2) in
          evaluate current_check (replace i e2 e1)
        | _ -> failwith "nonfunc applied"
      end
    | Func (a,e) ->
      Func (a,e)
    | Ctor (i,e) ->
      let v = evaluate current_check e in
      Ctor (i,v)
    | Match (e,i,branches) as match_expr ->
      let v = evaluate current_check e in
      begin match v with
        | Wildcard -> Wildcard
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
          let v = evaluate current_check (replace i (value_to_exp v) branch) in
          v
        | _ -> failwith "no soln"
      end
    | Fix (i,_,e') ->
      evaluate current_check (replace i e e')
    | Tuple es ->
      let vs =
        List.map ~f:(evaluate current_check) es
      in
      Tuple vs
    | Proj (i,e) ->
      let v = evaluate current_check e in
      begin match v with
        | Wildcard -> Wildcard
        | Tuple vs -> List.nth_exn vs i
        | _ -> failwith "bad"
      end
    | Unctor (i,e) ->
      let v = evaluate current_check e in
      begin match v with
        | Ctor (i',e) ->
          assert (Id.equal i  i');
          e
        | _ -> failwith "ah"
      end
  end
