open MyStdLib

let rec evaluate
    ~(tc:Context.Types.t)
    (e : Expr.t)
  : Value.t * Value.t list =
  match e with
  | Var i -> failwith ("unbound variable " ^ (Id.show i))
  | App (e1,e2) ->
    let (v1,v1s) = evaluate ~tc e1 in
    let e1 = Value.to_exp v1 in
    begin match e1 with
      | Expr.Func ((i,_),e1) ->
        let (v2,v2s) = evaluate ~tc e2 in
        let e2 = Value.to_exp v2 in
        let (v,vs) = evaluate ~tc (Expr.replace i e2 e1) in
        (v,v1s@v2s@vs)
      | _ -> failwith "nonfunc applied"
    end
  | Func (a,e) ->
    (Value.mk_func a e,[])
  | Ctor (i,e) ->
    let (v,vs) = evaluate ~tc e in
    (Value.mk_ctor i v,vs)
  | Match (e,i,branches) as match_expr ->
    let (v,vs) = evaluate ~tc e in
    let (choice,v) = Value.destruct_ctor_exn v in
    let branch_o = List.Assoc.find ~equal:Id.equal branches choice in
    let branch =
      begin match branch_o with
        | None ->
          failwith
            ("constructor "
             ^ (Id.show choice)
             ^ " not matched: \n "
             ^ (Expr.show match_expr))
        | Some b -> b
      end
    in
    let (v,vs') = evaluate ~tc (Expr.replace i (Value.to_exp v) branch) in
    (v,vs@vs')
  | Fix (i,_,e') ->
    evaluate ~tc (Expr.replace i e e')
  | Tuple es ->
    let (vs,vsaccs) =
      List.unzip
        (List.map ~f:(evaluate ~tc) es)
    in
    (Value.mk_tuple vs,List.concat vsaccs)
  | Proj (i,e) ->
    let (v,vs) = evaluate ~tc e in
    (List.nth_exn (Value.destruct_tuple_exn v) i,vs)

let evaluate_with_holes
    ~(tc:Context.Types.t)
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t * Value.t list =
  let e = Expr.replace_holes ~i_e e in
  evaluate ~tc e

let evaluate_basic
    ~(tc:Context.Types.t)
    (e:Expr.t)
  : Value.t =
  fst (evaluate ~tc e)

let evaluate_with_holes_basic
    ~(tc:Context.Types.t)
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t =
  let e = Expr.replace_holes ~i_e e in
  evaluate_basic ~tc e
