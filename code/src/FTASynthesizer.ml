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


  let perform_process
      ~(problem:Problem.t)
    : unit =
    let (args_t,res_t) = problem.synth_type in
    let checker =
      fun v1 v2 ->
        begin match List.Assoc.find ~equal:Value.equal problem.examples v1 with
          | Some v2' -> Value.equal v2 v2'
          | None -> true
        end
    in
    let c =
      C.initialize
        ~problem
        ([res_t;args_t]
         @(List.map ~f:Type.mk_named (Context.keys problem.tc))
         @(Context.data problem.ec))
        (List.map ~f:fst problem.examples)
        (fst problem.synth_type)
        checker
    in
    let vs =
      List.concat_map
        ~f:(fun (vs,v) ->
            List.map2_exn
              ~f:(ValueTCIntegration.tc_val problem.tc)
              ([v;vs])
              ([res_t;args_t]))
        problem.examples
    in
    let sub_vs =
      List.dedup_and_sort
        ~compare:ValueTCIntegration.Derivation.compare
        (List.concat_map
           ~f:ValueTCIntegration.Derivation.sub_derivations
           vs)
    in
    let vs_ts =
      List.filter_map
        ~f:(fun d ->
            let recursive =
              C.is_recursive_type
                c
                (ValueTCIntegration.Derivation.get_type d)
            in
            if recursive then
              Some (ValueTCIntegration.Derivation.get_value d
                   ,ValueTCIntegration.Derivation.get_type d)
            else
              None)
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
    let states_ts =
      List.concat_map
        ~f:(fun (v,t) ->
            List.map
              ~f:(fun inp -> ([(inp,v)],t))
              relevant_ins)
        vs_ts
    in
    let c =
      C.add_states
        c
        states_ts
    in
    let context_conversions =
      List.map
        ~f:(fun (i,e) ->
            let t = Context.find_exn problem.ec i in
            let (ins,out) = Type.split_to_arg_list_result t in
            let e = Expr.replace_holes ~i_e:(problem.eval_context) e in
            let evaluation vs =
              let es = List.map ~f:Value.to_exp vs in
              Eval.evaluate
                (List.fold
                  ~f:Expr.mk_app
                  ~init:e
                  es)
            in
            (FTAConstructor.Transition.FunctionApp i,evaluation,ins,out))
        problem.eval_context
    in
    let variant_conversions =
      (*** Ana, fill this in
        * nat_succ pseudocode:
        (Transition.FunctionApp "S", fun [v] -> Value.mk_ctor ("S", v), [nat], nat)
        * nat_zero psuedocode:
        (Transition.FunctionApp "O", fun [v] -> Value.mk_ctor ("O", v), [unit], nat)
        * bool_t pseudocode:
        (Transition.FunctionApp "True", fun [v] -> Value.mk_ctor ("True", v), [bool], bool)
        * bool_f pseudocode:
        (Transition.FunctionApp "False", fun [v] -> Value.mk_ctor ("False", v), [bool], bool)
      ***)
      [(FTAConstructor.Transition.VariantConstruct (MyStdLib.Id.Id "S"),
         (fun vs -> Value.mk_ctor (MyStdLib.Id.Id "S") (List.hd_exn vs)),
                             [Type.mk_named (MyStdLib.Id.Id "nat")], Type.mk_named (MyStdLib.Id.Id "nat"));
        (FTAConstructor.Transition.VariantConstruct (MyStdLib.Id.Id "O"),
         (fun vs -> Value.mk_ctor (MyStdLib.Id.Id "O") (List.hd_exn vs)),
                             [Type.mk_named (MyStdLib.Id.Id "unit")], Type.mk_named (MyStdLib.Id.Id "nat"));
        (FTAConstructor.Transition.VariantConstruct (MyStdLib.Id.Id "True"),
         (fun vs -> Value.mk_ctor (MyStdLib.Id.Id "True") (List.hd_exn vs)),
                             [Type.mk_named (MyStdLib.Id.Id "bool")], Type.mk_named (MyStdLib.Id.Id "bool"));
        (FTAConstructor.Transition.VariantConstruct (MyStdLib.Id.Id "False"),
         (fun vs -> Value.mk_ctor (MyStdLib.Id.Id "False") (List.hd_exn vs)),
                             [Type.mk_named (MyStdLib.Id.Id "bool")], Type.mk_named (MyStdLib.Id.Id "bool"))
        ]
    in
    let tuple_conversions =
      (* Fill this in too, though currently there's no test for them *)
      []
    in
    let conversions = context_conversions@variant_conversions@tuple_conversions in
    let c = C.update_from_conversions c conversions in
    let c = C.update_from_conversions c conversions in
    let c = C.add_destructors c in
    let c = C.add_let_ins c in
    let cs =
      List.map
        ~f:(fun (ins,out) ->
            let inp = ins in
            let c =
              (C.add_final_state
                 c
                 (C.val_state c [(inp,out)] res_t))
            in
            C.minimize c)
        problem.examples
    in
    let auts = List.map ~f:(fun c -> c.a) cs in
    let a =
      fold_on_head_exn
        ~f:(fun x y -> A.minimize (A.intersect x y))
        auts
    in
    let e = term_to_exp (A.pick_term a) in
    print_endline (Expr.show e);
    ()
end
