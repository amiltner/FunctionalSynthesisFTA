open MyStdLib
open Lang

let rec evaluate
    (e : Expr.t)
  : Value.t =
  let l = e.node in
  begin match l.eval with
    | None ->
      let ans =
        match Expr.node e with
        | Var i -> failwith ("unbound variable " ^ (Id.show i))
        | App (e1,e2) ->
          let (v1) = evaluate e1 in
          let e1 = Value.to_exp v1 in
          begin match Expr.destruct_func e1 with
            | Some ((i,_),e1) ->
              let (v2) = evaluate e2 in
              let e2 = Value.to_exp v2 in
              evaluate (Expr.replace i e2 e1)
            | None -> failwith "nonfunc applied"
          end
        | Func (a,e) ->
          Value.mk_func a e
        | Ctor (i,e) ->
          let v = evaluate e in
          Value.mk_ctor i v
        | Match (e,i,branches) as match_expr ->
          let v = evaluate e in
          let (choice,v) = Value.destruct_ctor_exn v in
          let branch_o = List.Assoc.find ~equal:Id.equal branches choice in
          let branch =
            begin match branch_o with
              | None ->
                failwith
                  ("constructor "
                   ^ (Id.show choice)
                   ^ " not matched: \n "
                   ^ (Expr.show_t_node match_expr))
              | Some b -> b
            end
          in
          let v = evaluate (Expr.replace i (Value.to_exp v) branch) in
          v
        | Fix (i,_,e') ->
          evaluate (Expr.replace i e e')
        | Tuple es ->
          let vs =
            List.map ~f:evaluate es
          in
          Value.mk_tuple vs
        | Proj (i,e) ->
          let v = evaluate e in
          (List.nth_exn (Value.destruct_tuple_exn v) i)
        | Unctor (i,e) ->
          let v = evaluate e in
          let (i',e) = Value.destruct_ctor_exn v in
          assert (Id.equal i  i');
          e
      in
      l.eval <- Some ans;
      ans
    | Some ans ->
      ans
  end

let evaluate_with_holes
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t =
  let e = Expr.replace_holes ~i_e e in
  evaluate e

let rec safe_evaluate
    (e:Expr.t)
  : Value.t option =
  try
    Some (evaluate e)
  with _ ->
    None
