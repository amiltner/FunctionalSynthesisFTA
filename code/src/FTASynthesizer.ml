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

  module Constraints =
  struct
    include DictOf(Value)(Spec)

    let lookup_default = lookup_default ~default:Spec.StandardConstraint

    let merge_single
        (c:t)
        (vin:Value.t)
        (vout:Value.t)
      : t option =
      begin match lookup_default c vin with
        | Spec.StandardConstraint ->
          Some
            (insert
               c
               vin
               (Spec.AddedConstraint vout))
        | Spec.AddedConstraint vout' ->
          if Value.equal vout vout' then
            Some c
          else
            None
      end

    let merge
        (c:t)
        (vinvouts:(Value.t * Value.t) list)
      : t option =
      List.fold
        ~f:(fun acco (vin,vout) ->
            begin match acco with
              | None -> None
              | Some acc ->
                merge_single acc vin vout
            end)
        ~init:(Some c)
        vinvouts
  end
  module ValToC = DictOf(Value)(C)
  module ValueSet = SetOf(Value)
  module StatePairSet = SetOf(PairOf(FTAConstructor.State)(FTAConstructor.State))

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
              C.get_final_values
                (ValToC.lookup_exn
                   inmap
                   v1)
                v1
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
      (all_ins:Value.t list)
      (required_vs:ValueSet.t)
      (constraints:Constraints.t)
    : (C.t * ValToC.t) =
    let inmap =
      List.fold
        ~f:(fun inmap v ->
            let s = Constraints.lookup_default constraints v in
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
    (c,inmap)

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

  module PQE = struct
    module Priority = IntModule

    type t =
      {
        inputs       : ValueSet.t     ;
        c            : C.t            ;
        constraints  : Constraints.t  ;
        nonpermitted : StatePairSet.t ;
        rep          : A.TermState.t  ;
        v_to_c       : ValToC.t       ;
      }
    [@@deriving eq, hash, ord, show]

    let make
        ~(inputs:ValueSet.t)
        ~(c:C.t)
        ~(constraints:Constraints.t)
        ~(nonpermitted:StatePairSet.t)
        ~(v_to_c:ValToC.t)
      : t option =
      let rep_o = C.min_term_state c in
      Option.map
        ~f:(fun rep ->
            {
              inputs       ;
              c            ;
              constraints  ;
              nonpermitted ;
              rep          ;
              v_to_c       ;
            })
        rep_o

    let update_nonpermitted
        (qe:t)
        ((s1,s2) as t:FTAConstructor.State.t * FTAConstructor.State.t)
      : t option =
      let c =
        C.remove_transition
          qe.c
          FTAConstructor.Transition.rec_
          [s1]
          s2
      in
      let nonpermitted =
        StatePairSet.insert
          t
          qe.nonpermitted
      in
      make
        ~inputs:qe.inputs
        ~c
        ~constraints:qe.constraints
        ~nonpermitted
        ~v_to_c:qe.v_to_c

    let priority
        (qe:t)
      : int =
      Expr.size (term_to_exp (A.TermState.to_term qe.rep))

    let to_string_legible
        (qe:t)
      : string =
      let es = Expr.show (term_to_exp (A.TermState.to_term qe.rep)) in
      let cs = Constraints.show qe.constraints in
      "term: " ^ es ^ "\nconstraints: " ^ cs
  end

  module PQ = PriorityQueueOf(PQE)

  let safely_restricts_in_c
      (c:C.t)
      (inchoice:Value.t)
      (restriction:Value.t)
    : bool option =
    (*None means unsafe restriction, Some true means restricts outputs, false means no restricts outputs*)
    let vouts = C.get_final_values c inchoice in
    if List.mem ~equal:Value.equal vouts restriction then
      Some (List.length vouts = 1)
    else
      (None)

  let safely_restricts_outputs
        (int_c:C.t)
        (inset:ValueSet.t)
        (vtoc:ValToC.t)
        (inchoice:Value.t)
        (restriction:Value.t)
    : bool option =
    if ValueSet.member inset inchoice then
      safely_restricts_in_c int_c inchoice restriction
    else
      safely_restricts_in_c
        (ValToC.lookup_exn vtoc inchoice)
        inchoice
        restriction


  let synth
      ~(problem:Problem.t)
    : Expr.t =
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
              1
            else
              Value.compare v1 v2)
        all_inputs
    in
    let rec extract_recursive_calls
        (ts:A.TermState.t)
      : (FTAConstructor.State.t * FTAConstructor.State.t) list =
      begin match ts with
        | TS ((FTAConstructor.Transition.Rec,1),target,[source_ts]) ->
          (A.TermState.get_state source_ts,target)::(extract_recursive_calls source_ts)
        | TS (_,_,tss) ->
          List.concat_map
            ~f:extract_recursive_calls
            tss
      end
    in
    let process_queue_element
        (pqe:PQE.t)
      : (PQE.t list , Expr.t) either =
      Consts.log (fun _ -> "\n\nPopped:");
      Consts.log (fun _ -> PQE.to_string_legible pqe);
      let c = pqe.c in
      let ts = pqe.rep in
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
      let approvals =
        List.map
          ~f:(fun (v1,v2) ->
              Option.map
                ~f:(fun ro -> (ro,(v1,v2)))
                (safely_restricts_outputs c pqe.inputs pqe.v_to_c v1 v2))
          rrs
      in
      let possible =
        distribute_option
          approvals
      in
      begin match possible with
        | Some bs ->
          let new_constraints =
            List.filter_map
              ~f:(fun (b,nc) ->
                  if b then
                    None
                  else
                    Some nc)
              bs
          in
          if List.length new_constraints = 0 then
            let e = term_to_exp (A.TermState.to_term ts) in
            Right e
          else
            let merged_constraints_o =
              Constraints.merge
                pqe.constraints
                new_constraints
            in
            begin match merged_constraints_o with
              | None ->
                Left []
              | Some merged_constraints ->
                Consts.log (fun _ -> "constraints were merged");
                Consts.log (fun _ -> "new constraints: ");
                Consts.log
                  (fun _ ->
                     List.to_string
                       ~f:(string_of_pair Value.show Value.show)
                       new_constraints);
                let inputs =
                  ValueSet.insert_all
                    pqe.inputs
                    (List.map ~f:fst new_constraints)
                in
                let (c,v_to_c) =
                  construct_full
                    ~problem
                    sorted_inputs
                    inputs
                    merged_constraints
                in
                let qe =
                  PQE.make
                    ~inputs:pqe.inputs
                    ~c
                    ~constraints:merged_constraints
                    ~nonpermitted:StatePairSet.empty
                    ~v_to_c
                in
                Left (Option.to_list qe)
            end
        | None ->
          Consts.log (fun _ -> "popped value was found impossible");
          Left
            (List.filter_map
               ~f:(fun r ->
                   PQE.update_nonpermitted
                     pqe
                     r)
               rcs)
      end
    in
    let rec find_it_out
        (specs:PQ.t)
      : Expr.t =
      begin match PQ.pop specs with
        | Some (pqe,_,specs) ->
          begin match process_queue_element pqe with
            | Left new_qes ->
              find_it_out (PQ.push_all specs new_qes)
            | Right e -> e
          end
        | None -> failwith "no satisfying found"
      end
    in
    let inputs = ValueSet.from_list chosen_inputs in
    let (c,v_to_c) =
      construct_full
        ~problem
        sorted_inputs
        inputs
        Constraints.empty
    in
    let qe =
      PQE.make
        ~inputs
        ~c
        ~constraints:Constraints.empty
        ~nonpermitted:StatePairSet.empty
        ~v_to_c
    in
    find_it_out (PQ.from_list (Option.to_list qe))
end
