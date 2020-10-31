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

  module IntersectionCache = DictOf(ListOf(Spec))(C)

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

  module ValToSpec = DictOf(Value)(Spec)
  module ValToC = DictOf(Value)(C)
  module ValueSet = SetOf(Value)

  let construct_initial_fta
      ~(problem:Problem.t)
      (inmap:ValToC.t)
      (i:Value.t)
      (s:Spec.t)
    : C.t =
    let standard_checker =
      fun v1 v2 ->
        begin match List.Assoc.find ~equal:Value.equal problem.examples v1 with
          | Some v2' -> Value.equal v2 v2'
          | None -> true
        end
    in
    let checker =
      begin match s with
        | StandardConstraint -> standard_checker
        | AddedConstraint v ->
          fun v1 v2 ->
            if Value.equal v1 i then
              Value.equal v2 v
            else
              standard_checker v1 v2
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
                (ValToC.lookup_exn
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

  let construct_full
      ~(problem:Problem.t)
      (all_ins:Value.t list)
      (required_vs:ValueSet.t)
      (v_to_spec:ValToSpec.t)
    : C.t =
    let inmap =
      List.fold
        ~f:(fun inmap v ->
            let s = ValToSpec.lookup_default ~default:Spec.StandardConstraint v_to_spec v in
            let res =
              construct_initial_fta
                ~problem
                inmap
                v
                s
            in
            ValToC.insert
              inmap
              v
              res)
        ~init:ValToC.empty
        all_ins
    in
    let cs =
      List.map
        ~f:(ValToC.lookup_exn inmap)
        (ValueSet.as_list required_vs)
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

  let safely_restricts_outputs
      (c:C.t)
      (restriction:Value.t)
    : bool option =
    (*None means unsafe restriction, Some true means restricts outputs, false means no restricts outputs*)
    let vouts = C.get_final_values c in
    if List.mem ~equal:Value.equal vouts restriction then
      Some (List.length vouts = 1)
    else
      None

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
    (*let inmap =
      List.fold
        ~f:(fun inmap v ->
            let res =
              construct_initial_fta
                ~problem
                inmap
                (Spec.standard_constraint v)
            in
            SpecToC.insert
              inmap
              (Spec.standard_constraint v)
              res)
        ~init:SpecToC.empty
        sorted_inputs
    in
    let cs =
      List.map
        ~f:(SpecToC.lookup_exn inmap)
        (List.map ~f:Spec.standard_constraint chosen_inputs)
    in
    let _ =
      fold_on_head_exn
        ~f:(fun x y ->
            let inted = (C.intersect x y) in
            C.minimize inted)
        cs
      in*)
    let rec extract_recursive_calls
        (ts:C.TermState.t)
      : (FTAConstructor.State.t * FTAConstructor.State.t) list =
      begin match ts with
        | TS ((FTAConstructor.Transition.Rec,1),target,[source_ts]) ->
          (C.TermState.get_state source_ts,target)::(extract_recursive_calls source_ts)
        | TS (_,_,tss) ->
          List.concat_map
            ~f:extract_recursive_calls
            tss
      end
    in
    let rec find_it_out
        (specs:(ValueSet.t * ValToSpec.t) list)
      : unit =
      begin match specs with
        | [] -> failwith "no valid specs"
        | (vs,vts)::_ ->
          let c =
            construct_full
              ~problem
              sorted_inputs
              vs
              vts
          in
          let ts = C.min_term_state c in
          let rcs =
            List.dedup_and_sort
              ~compare:(pair_compare FTAConstructor.State.compare FTAConstructor.State.compare)
              (extract_recursive_calls ts)
          in
          let rrs =
            List.concat_map
              ~f:(uncurry extract_recursive_requirements)
              rcs
          in
          List.iter
            ~f:(fun (s1,s2) ->
                print_endline "input:";
                print_endline (Value.show s1);
                print_endline "output:";
                print_endline (Value.show s2);
                print_endline "\n")
            rrs;
          let e = term_to_exp (C.TermState.to_term ts) in
          print_endline (Expr.show e);
          ()
      end
    in
    find_it_out
      [(ValueSet.from_list chosen_inputs
       ,ValToSpec.empty)]
end
