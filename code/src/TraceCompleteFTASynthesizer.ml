open MyStdLib
open Lang

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
      List.concat_map
        ~f:(fun (i,e) ->
            let t = Context.find_exn problem.ec i in
            let (ins,out) = Type.split_to_arg_list_result t in
            let ins =
              List.map
                ~f:(fun int -> (int,TermClassification.Introduction))
                ins
            in
            let e = Expr.replace_holes ~i_e:problem.eval_context e in
            let evaluation vs =
              let es = List.map ~f:Value.to_exp vs in
              [Eval.evaluate
                 (List.fold
                    ~f:Expr.mk_app
                    ~init:e
                    es)]
            in
            [(FTAConstructor.Transition.FunctionApp i,evaluation,ins,(out,TermClassification.Elimination))
            ;(FTAConstructor.Transition.FunctionApp i,evaluation,ins,(out,TermClassification.Introduction))])
        problem.eval_context
    in
    let variant_construct_conversions =
      List.concat_map
        ~f:(fun t ->
            match Type.node t with
            | Type.Variant l ->
              List.map
                ~f:(fun (i,t') ->
                    (FTAConstructor.Transition.VariantConstruct i
                    ,(fun vs -> [Value.mk_ctor i (List.hd_exn vs)])
                    ,[(t',TermClassification.Introduction)]
                    ,(t,TermClassification.Introduction)))
                l
            | _ -> [])
        (C.get_all_types c)
    in
    let variant_unsafe_destruct_conversions =
      List.concat_map
        ~f:(fun t ->
            match Type.node t with
            | Type.Variant l ->
              List.map
                ~f:(fun (i,t') ->
                    (FTAConstructor.Transition.UnsafeVariantDestruct i,
                     (fun vs ->
                        match Value.destruct_ctor (List.hd_exn vs) with
                        | Some (i',v) ->
                          if Id.equal i i' then [v] else []
                        | _ -> [])
                    ,[(t,TermClassification.Elimination)]
                    ,(t',TermClassification.Elimination)))
                l
            | _ -> [])
        (C.get_all_types c)
    in
    let tuple_constructors =
      List.filter_map
        ~f:(fun t ->
            match Type.node t with
            | Type.Tuple ts ->
              let ts =
                List.map
                  ~f:(fun t -> (t,TermClassification.Introduction))
                  ts
              in
              Some (FTAConstructor.Transition.TupleConstruct (List.length ts)
                   ,(fun vs -> [Value.mk_tuple vs])
                   ,ts
                   ,(t,TermClassification.Introduction))
            | _ -> None)
        (C.get_all_types c)
    in
    let tuple_destructors =
      List.concat_map
        ~f:(fun t ->
            begin match Type.node t with
              | Type.Tuple ts ->
                List.concat_mapi
                  ~f:(fun i tout ->
                      [(FTAConstructor.Transition.TupleDestruct (List.length ts,i)
                       ,(fun vs ->
                          [List.nth_exn (Value.destruct_tuple_exn (List.hd_exn vs)) i])
                       ,[(t,TermClassification.Elimination)]
                       ,(tout,TermClassification.Elimination))
                      ;(FTAConstructor.Transition.TupleDestruct (List.length ts,i)
                       ,(fun vs ->
                          [List.nth_exn (Value.destruct_tuple_exn (List.hd_exn vs)) i])
                       ,[(t,TermClassification.Elimination)]
                       ,(tout,TermClassification.Introduction))])
                  ts
              | _ -> []
            end)
        (C.get_all_types c)
    in
    let rec_call_conversions =
      let evaluation vs =
        begin match vs with
          | [v1] ->
            let break = fun v ->
              let t =
                Typecheck.typecheck_value
                  problem.ec
                  problem.tc
                  problem.vc
                  v
              in
              C.is_recursive_type
                c
                t
            in
            if Value.strict_functional_subvalue ~break v1 i then
              [List.Assoc.find_exn ~equal:Value.equal inmap v1]
            else
              []
          | _ -> failwith "invalid"
        end
           in
           [(FTAConstructor.Transition.Rec
            ,evaluation
            ,[(args_t,TermClassification.Introduction)]
            ,(res_t,TermClassification.Elimination))
           ;(FTAConstructor.Transition.Rec
            ,evaluation
            ,[(args_t,TermClassification.Introduction)]
            ,(res_t,TermClassification.Introduction))]
         in
    let conversions =
      context_conversions
      @ variant_construct_conversions
      @ tuple_constructors
      @ tuple_destructors
      @ rec_call_conversions
      @ variant_unsafe_destruct_conversions
    in
    let examples =
      begin match problem.spec with
        | IOEs vs -> vs
        | _ -> failwith "not ready yet"
      end
    in
    let subcall_sites =
      List.filter_map
        ~f:(fun (i',_) ->
            if Value.strict_subvalue i' i then
              Some ([(i,i')],(args_t,TermClassification.Elimination))
            else
              None)
        examples
    in
    let c = C.add_states c subcall_sites in
    let c =
      List.fold
        ~f:(fun c _ ->
            C.update_from_conversions c conversions)
        ~init:c
        (range 0 num_applications)
    in
    let c = C.add_destructors c in
    let c = C.minimize c in
    c

  module S = FTASynthesizer.Create(B)

  let construct_full
      ~(problem:Problem.t)
      (num_applications:int)
    : S.C.t =
    let examples =
      begin match problem.spec with
        | IOEs vs -> vs
        | _ -> failwith "not ready yet"
      end
    in
    let spec = examples in
    let cs =
      List.map
        ~f:(fun (vin,vout) ->
            S.construct_single_fta
              ~problem
              (fun v -> [List.Assoc.find_exn ~equal:Value.equal examples v])
              vin
              (fun v1 v2 -> Value.equal v1 vin && Value.equal v2 vout)
            (*construct_initial_fta
              ~problem
              spec
              vin
              vout*)
              num_applications)
        spec
    in
    let c =
      merge_by_size_applies_exn
        ~compare:(fun c1 c2 ->
            let s1 = S.C.size c1 in
            let s2 = S.C.size c2 in
            Int.compare s1 s2)
        ~merge:(fun x y ->
            let inted = S.C.intersect x y in
            S.C.minimize inted)
        ~needs_merge:(fun max cand ->
            let max_tso = S.C.min_term_state max in
            begin match max_tso with
              | None -> true
              | Some ts ->
                let t = A.TermState.to_term ts in
                not (S.C.accepts_term cand t)
            end)
        cs
    in
    c

  let rec synth_internal
      ~(problem:Problem.t)
      (current:int)
    : Expr.t =
    let c =
      construct_full
        ~problem
        current
    in
    let st = S.C.min_term_state c in
    begin match st with
      | None -> synth_internal ~problem (current+2)
      | Some st -> C.term_to_exp_internals (A.TermState.to_term st)
    end

  let synth
      ~(problem:Problem.t)
    : Expr.t =
    synth_internal ~problem 4
end
