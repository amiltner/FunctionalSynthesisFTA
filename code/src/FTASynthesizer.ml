open MyStdLib

module Create(B : Automata.AutomatonBuilder) = struct
  module A = B(FTAConstructor.Transition)(FTAConstructor.State)
  module C = FTAConstructor.Make(A)

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
          | _ -> failwith "incorrect"
        end
      | TupleConstruct ->
        failwith "ah"
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
    end

  module ValueToC = DictOf(Value)(C)

  let construct_initial_fta
      ~(problem:Problem.t)
      (inmap:ValueToC.t)
      (i:Value.t)
    : C.t =
    let checker =
      fun v1 v2 ->
        begin match List.Assoc.find ~equal:Value.equal problem.examples v1 with
          | Some v2' -> Value.equal v2 v2'
          | None -> true
        end
    in
    let (args_t,res_t) = problem.synth_type in
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
    let variant_conversions =
      (* Ana, fill this in *)
      []
    in
    let tuple_conversions =
      (* Fill this in too, though currently there's no test for them *)
      []
    in
    let rec_call_conversions =
      let evaluation vs =
        begin match vs with
          | [v1] ->
            if Value.strict_subvalue v1 i then
              C.get_final_values
                (ValueToC.lookup_exn
                   inmap
                   v1)
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
    let conversions = context_conversions@variant_conversions@tuple_conversions@rec_call_conversions in
    let c =
      C.initialize
        ~problem
        ([res_t;args_t]
         @(List.map ~f:Type.mk_named (Context.keys problem.tc))
         @(Context.data problem.ec))
        [i]
        (fst problem.synth_type)
        checker
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
    (*let c = C.update_from_conversions c rec_call_conversions in*)
    let c = C.update_from_conversions c conversions in
    let c = C.update_from_conversions c conversions in
    let c = C.add_destructors c in
    (*let c = C.add_let_ins c in*)
    (*let c = C.add_final_state c (C.val_state c [(i,o)] res_t) in*)
    let c = C.minimize c in
    c

  let get_all_subvalues_of_same_type
      ~(problem:Problem.t)
      (args_t:Type.t)
      (v:Value.t)
    : Value.t list =
    let vtc = ValueTCIntegration.tc_val (problem.tc) v args_t in
    let sub_vs =
      List.dedup_and_sort
        ~compare:ValueTCIntegration.Derivation.compare
        (ValueTCIntegration.Derivation.sub_derivations vtc)
    in
    let vs_ts =
      List.map
        ~f:(fun d ->
            (ValueTCIntegration.Derivation.get_value d
            ,ValueTCIntegration.Derivation.get_type d))
        sub_vs
    in
    let relevant_ins =
      List.filter_map
        ~f:(fun (v,t) ->
            let is_relevant =
              Typecheck.type_equiv
                problem.tc
                t
                args_t
            in
            if is_relevant then
              Some v
            else
              None)
        vs_ts
    in
    relevant_ins

  let other_alg
      ~(problem:Problem.t)
    : unit =
    let chosen_inputs = List.map ~f:fst problem.examples in
    let all_inputs =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map
           ~f:(get_all_subvalues_of_same_type ~problem (fst problem.synth_type))
           chosen_inputs)
    in
    (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
     then v1 comes before v2 in terms of generating their FTAs. This is
     necessrary for ensuring that recursion is appropriately added *)
    let sorted_inputs =
      List.dedup_and_sort
        ~compare:(fun v1 v2 ->
            if Value.strict_subvalue v1 v2 then
              -1
            else if Value.strict_subvalue v2 v1 then
              -1
            else
              Value.compare v1 v2)
        all_inputs
    in
    let inmap =
      List.fold
        ~f:(fun inmap v ->
            let res =
              construct_initial_fta
                ~problem
                inmap
                v
            in
            ValueToC.insert
              inmap
              v
              res)
        ~init:ValueToC.empty
        sorted_inputs
    in
    let cs =
      List.map
        ~f:(ValueToC.lookup_exn inmap)
        chosen_inputs
    in
    let c =
      fold_on_head_exn
        ~f:(fun x y ->
            let inted = (C.intersect x y) in
            C.minimize inted)
        cs
    in
    let e = term_to_exp (C.min_tree' c) in
    print_endline (Expr.show e);
    ()
end
