open MyStdLib

module Create(B : Automata.AutomatonBuilder) = struct
  module A = B(FTAConstructor.Transition)(FTAConstructor.State)
  module C = FTAConstructor.Make(A)

  module Spec =
  struct
    type t =
      | StandardConstraint
      | AddedConstraint of Value.t
    [@@deriving eq, hash, ord, show]
  end

  let rec term_to_exp
      (Term ((s,_),ts):A.term)
    : Expr.t =
    begin match s with
      | FunctionApp i ->
        List.fold
          ~f:(fun acc bt ->
              Expr.mk_app
                acc
                (term_to_exp bt))
          ~init:(Expr.mk_var i)
          ts
      | VariantConstruct c ->
        begin match ts with
          | [t] ->
            Expr.mk_ctor c (term_to_exp t)
          | _ -> failwith "incorrect setup"
        end
      | UnsafeVariantDestruct c ->
        begin match ts with
          | [t] ->
            Expr.mk_app
              (Expr.mk_var (Id.create ("destruct" ^ Id.to_string c)))
              (term_to_exp t)
          | _ -> failwith "incorrect setup"
        end
      | TupleConstruct _ ->
        Expr.mk_tuple
          (List.map
             ~f:term_to_exp
             ts)
      | Var ->
        Expr.mk_var (Id.create "x")
      | LetIn ->
        failwith "not permitted"
      | Rec ->
        begin match ts with
          | [t] ->
            Expr.mk_app (Expr.mk_var (Id.create "f")) (term_to_exp t)
          | _ -> failwith "incorrect"
        end
      | IfThenElse ->
        (* TODO, make destructors *)
        List.fold
          ~f:(fun acc bt ->
              Expr.mk_app
                acc
                (term_to_exp bt))
          ~init:(Expr.mk_var (Id.create "ifthenelse"))
          ts
      | VariantSwitch _ ->
        (* TODO, make destructors *)
        List.fold
          ~f:(fun acc bt ->
              Expr.mk_app
                acc
                (term_to_exp bt))
          ~init:(Expr.mk_var (Id.create "vmatch"))
          ts
      | TupleDestruct (_,i) ->
        Expr.mk_proj i (term_to_exp (List.hd_exn ts))
    end

  let construct_initial_fta
      ~(problem:Problem.t)
      (inmap:(Value.t * Value.t) list)
      (i:Value.t)
      (vout:Value.t)
      (num_applications:int)
    : C.t =
    let checker =
      fun v1 v2 ->
        begin match List.Assoc.find ~equal:Value.equal inmap v1 with
          | None -> true
          | Some v2' -> Value.equal v2 v2'
        end
    in
    let (args_t,res_t) = problem.synth_type in
    let c =
      C.initialize
        ~problem
        ([res_t;args_t]
         @(List.map ~f:Type.mk_named (Context.keys problem.tc))
         @(Context.data problem.ec))
        [i]
        problem.synth_type
        checker
    in
    let context_conversions =
      List.map
        ~f:(fun (i,e) ->
            let t = Context.find_exn problem.ec i in
            let (ins,out) = Type.split_to_arg_list_result t in
            let e = Expr.replace_holes ~i_e:(problem.eval_context) e in
            let evaluation vs =
              let es = List.map ~f:Value.to_exp vs in
              [Eval.evaluate
                 (List.fold
                    ~f:Expr.mk_app
                    ~init:e
                    es)]
            in
            (FTAConstructor.Transition.FunctionApp i,evaluation,ins,out))
        problem.eval_context
    in
    let make_conversion_with i t t' =
      (FTAConstructor.Transition.VariantConstruct i,
       (fun vs -> [Value.mk_ctor i (List.hd_exn vs)]),
       [t'], t)
    in
    let variant_construct_conversions =
      List.concat_map
        ~f:(fun t ->
            match t with
            | Type.Variant l ->
              List.map
                ~f:(fun (i,t') -> make_conversion_with i t t')
                l
            | _ -> [])
        (C.get_all_types c)
    in
    let make_destruct_conversion_with i t t' =
      (FTAConstructor.Transition.UnsafeVariantDestruct i,
       (fun vs ->
          match Value.destruct_ctor (List.hd_exn vs) with
          | Some (i',v) ->
            if Id.equal i i' then [v] else []
          | _ -> []),
       [t], t')
    in
    let variant_unsafe_destruct_conversions =
      List.concat_map
        ~f:(fun t ->
            match t with
            | Type.Variant l ->
              List.map
                ~f:(fun (i,t') -> make_destruct_conversion_with i t t')
                l
            | _ -> [])
        (C.get_all_types c)
    in
    let tuple_constructors =
      List.filter_map
        ~f:(fun t ->
            match t with
            | Type.Tuple ts ->
              Some (FTAConstructor.Transition.TupleConstruct t
                   ,(fun vs -> [Value.mk_tuple vs])
                   ,ts
                   ,t)
            | _ -> None)
        (C.get_all_types c)
    in
    let tuple_destructors =
      List.concat_map
        ~f:(fun t ->
            begin match t with
              | Type.Tuple ts ->
                List.mapi
                  ~f:(fun i tout ->
                      (FTAConstructor.Transition.TupleDestruct (t,i)
                      ,(fun vs ->
                         [List.nth_exn (Value.destruct_tuple_exn (List.hd_exn vs)) i])
                      ,[t]
                      ,tout))
                  ts
              | _ -> []
            end)
        (C.get_all_types c)
    in
    let rec_call_conversions =
      let evaluation vs =
        begin match vs with
          | [v1] ->
            if Value.strict_subvalue v1 i then
              [List.Assoc.find_exn ~equal:Value.equal inmap v1]
            else
              []

          | _ -> failwith "invalid"
        end
      in
      [(FTAConstructor.Transition.Rec
       ,evaluation
       ,[args_t]
       ,res_t)]
    in
    let conversions =
      context_conversions
      @ variant_construct_conversions
      @ tuple_constructors
      @ tuple_destructors
      @ rec_call_conversions
      @ variant_unsafe_destruct_conversions
    in
    let subcall_sites =
      List.filter_map
        ~f:(fun (i',_) ->
            if Value.strict_subvalue i' i then
              Some ([(i,i')],args_t)
            else
              None)
        problem.examples
    in
    let c = C.add_states c subcall_sites in
    let c = C.update_from_conversions c conversions in
    let c = C.update_from_conversions c conversions in
    let c = C.update_from_conversions c conversions in
    let c = C.update_from_conversions c conversions in
    let c = C.update_from_conversions c conversions in
    let c = C.add_destructors c in
    let c = C.minimize c in
    c

  let construct_full
      ~(problem:Problem.t)
      (num_applications:int)
    : C.t =
    let spec = problem.examples in
    let cs =
      List.map
        ~f:(fun (vin,vout) ->
            construct_initial_fta
              ~problem
              spec
              vin
              vout
              num_applications)
        spec
    in
    let c =
      fold_on_head_exn
        ~f:(fun x y ->
            let inted = (C.intersect x y) in
            C.minimize inted)
        cs
    in
    c

  let extract_recursive_requirements
      (sin:FTAConstructor.State.t)
      (sout:FTAConstructor.State.t)
    : (Value.t * Value.t) list =
    begin match (FTAConstructor.State.destruct_vals sin,FTAConstructor.State.destruct_vals sout) with
      | (Some (vvsin,_), Some (vvsout,_)) ->
        let ins = List.map ~f:snd vvsin in
        let outs = List.map ~f:snd vvsout in
        let inouts = List.zip_exn ins outs in
        inouts
      | _ -> failwith "when would this happen?"
    end

  let rec synth_internal
      ~(problem:Problem.t)
      (current:int)
    : Expr.t =
    let c =
      construct_full
        ~problem
        current
    in
    let st = C.min_term_state c in
    begin match st with
      | None -> synth_internal ~problem (current+3)
      | Some st -> term_to_exp (A.TermState.to_term st)
    end

  let synth
      ~(problem:Problem.t)
    : Expr.t =
    synth_internal ~problem 5
end
