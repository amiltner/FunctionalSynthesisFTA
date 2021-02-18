open MyStdLib
open Lang

module Create(B : Automata.AutomatonBuilder) (*: Synthesizers.PredicateSynth.S *)= struct
  module A = B(FTAConstructor.Transition)(FTAConstructor.State)
  module C = FTAConstructor.Make(A)

  module AbstractionDict =
  struct
    include DictOf(Value)(Abstraction)

    let lookup
        (d:t)
        (k:key)
      : value =
      lookup_default ~default:Abstraction.init d k

    let integrate_refinement
        (ad:t)
        (vps:(Value.t * Type.t * Predicate.t) list)
      : t =
      List.fold
        ~f:(fun ad (v,t,p) ->
            let va = lookup ad v in
            let va = Abstraction.add va t p in
            insert ad v va)
        ~init:ad
        vps
  end

  type t =
    {
      context : Context.t ;
      tin : Type.t ;
      tout : Type.t ;
    }

  let init
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
    : t =
    {
      context ;
      tin ;
      tout ;
    }

  let context
      (a:t)
    : Context.t =
    a.context

  let tin
      (a:t)
    : Type.t =
    a.tin

  let tout
      (a:t)
    : Type.t =
    a.tout

  module Spec =
  struct
    type t =
      | StandardConstraint
      | AddedConstraint of Value.t
    [@@deriving eq, hash, ord, show]
  end

  module IntersectionCache = DictOf(ListOf(Spec))(C)

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

  (*TODO: this is really ugly right now, I need to clean it up badly*)
  let subvalues_full_of_same_type
      ~(context:Context.t)
      ~(break:Value.t -> bool)
      (v:Value.t)
    : Value.t list =
    let t = Typecheck.typecheck_value context.ec context.tc context.vc v in
    let subvalues_full = Value.functional_subvalues ~break v in
    List.filter
      ~f:(fun v ->
          Typecheck.type_equiv
            context.tc
            (Typecheck.typecheck_value context.ec context.tc context.vc v)
            t)
      subvalues_full

  let construct_single_fta
      ~(context:Context.t)
      ~(abstraction:Abstraction.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      (sub_calls:Value.t -> Value.t list)
      (input:Value.t)
      (valid_ios:Value.t -> Value.t -> bool)
      (num_applications:int)
    : C.t =
    Consts.time
      Consts.initial_creation_time
      (fun _ ->
         let c =
           C.initialize_context
             ~context
             ~abstraction
             ([tin;tout]
              @(List.map ~f:Type.mk_named (Context.keys context.tc))
              @(Context.data context.ec)
              @(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) (Value.subvalues input)))
             [input]
             (tin,tout)
             valid_ios
         in
         let context_conversions =
           List.concat_map
             ~f:(fun (i,e) ->
                 let t = Context.find_exn context.ec i in
                 let (ins,out) = Type.split_to_arg_list_result t in
                 let ins =
                   List.map
                     ~f:(fun int -> (int,TermClassification.Introduction))
                     ins
                 in
                 let e = Expr.replace_holes ~i_e:context.evals e in
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
             context.evals
         in
         let eval_conversion =
           List.concat_map
             ~f:(fun t ->
                 match Type.node t with
                 | Type.Arrow (t1,t2) ->
                   let evaluate vs =
                     begin match vs with
                       | [f;e] ->
                         let f = Value.to_exp f in
                         let e = Value.to_exp e in
                         [Eval.evaluate (Expr.mk_app f e)]
                       | _ -> failwith "bad"
                     end
                   in
                   [(FTAConstructor.Transition.Apply
                    ,evaluate
                    ,[(t,TermClassification.Elimination)
                     ;(t1,TermClassification.Introduction)]
                    ,(t2,TermClassification.Elimination))
                   ;(FTAConstructor.Transition.Apply
                    ,evaluate
                    ,[(t,TermClassification.Elimination)
                     ;(t1,TermClassification.Introduction)]
                    ,(t2,TermClassification.Introduction))]
                 | _ -> [])
           (C.get_all_types c)
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
                   List.concat_map
                     ~f:(fun (i,t') ->
                         [(FTAConstructor.Transition.UnsafeVariantDestruct i,
                           (fun vs ->
                              match Value.destruct_ctor (List.hd_exn vs) with
                              | Some (i',v) ->
                                if Id.equal i i' then [v] else []
                              | _ -> [])
                          ,[(t,TermClassification.Elimination)]
                          ,(t',TermClassification.Elimination))
                         ;(FTAConstructor.Transition.UnsafeVariantDestruct i,
                           (fun vs ->
                              match Value.destruct_ctor (List.hd_exn vs) with
                              | Some (i',v) ->
                                if Id.equal i i' then [v] else []
                              | _ -> [])
                          ,[(t,TermClassification.Elimination)]
                          ,(t',TermClassification.Introduction))])
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
                               [begin match Value.node (List.hd_exn vs) with
                                  | Tuple vs ->
                                    List.nth_exn vs i
                                  | Wildcard ->
                                    Value.mk_wildcard
                                  | _ -> failwith "invalid"
                                end])
                            ,[(t,TermClassification.Elimination)]
                            ,(tout,TermClassification.Elimination))
                           ;(FTAConstructor.Transition.TupleDestruct (List.length ts,i)
                            ,(fun vs ->
                               [begin match Value.node (List.hd_exn vs) with
                                  | Tuple vs ->
                                    List.nth_exn vs i
                                  | Wildcard ->
                                    Value.mk_wildcard
                                  | _ -> failwith "invalid"
                                end])
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
                         context.ec
                         context.tc
                         context.vc
                         v
                     in
                     C.is_recursive_type
                       c
                       t
                 in
                 if Value.strict_functional_subvalue ~break v1 input then
                   sub_calls v1
                 else
                   []
               | _ -> failwith "invalid"
             end
           in
           [(FTAConstructor.Transition.Rec
            ,evaluation
            ,[(tin,TermClassification.Introduction)]
            ,(tout,TermClassification.Elimination))
           ;(FTAConstructor.Transition.Rec
            ,evaluation
            ,[(tin,TermClassification.Introduction)]
            ,(tout,TermClassification.Introduction))]
         in
         let conversions =
           context_conversions
           @ variant_construct_conversions
           @ tuple_constructors
           @ eval_conversion
           @ tuple_destructors
           @ rec_call_conversions
           @ variant_unsafe_destruct_conversions
         in
         (*let destruct_conversions =
           tuple_destructors
           @ variant_unsafe_destruct_conversions
         in
         let construct_conversions =
           tuple_constructors
           @ variant_construct_conversions
           in*)
         (*let subvalues =
           subvalues_full_of_same_type
             ~context
             ~break:(fun v ->
                 let t =
                   Typecheck.typecheck_value
                     context.ec
                     context.tc
                     context.vc
                     v
                 in
                 C.is_recursive_type
                   c
                   t)
             input
         in
         let subcall_sites =
           List.filter_map
             ~f:(fun i' ->
                 if Value.strict_subvalue i' input then
                   Some ([(input,i')],tin)
                 else
                   None)
             subvalues
         in
           let c = C.add_states c subcall_sites in*)
           List.iter
             ~f:(fun _ ->
                 C.update_from_conversions c variant_unsafe_destruct_conversions;
                 C.update_from_conversions c tuple_destructors;
                 C.update_from_conversions c conversions)
             (range 0 num_applications);
         (*C.update_from_conversions c (destruct_conversions) ~ensure_state:false;*)
           C.add_destructors c;
           (*print_endline "here";
             print_endline (C.show c);
             print_endline (string_of_bool (Option.is_some (C.min_term_state c)));*)
         let c = C.minimize c in
           (*print_endline (C.show c);
             print_endline "there";*)
         c)

  let checker_from_exp
      (e:Expr.t)
      (v1:Value.t)
      (v2:Value.t)
    : bool =
    let e1 = Value.to_exp v1 in
    let e2 = Value.to_exp v2 in
    let vres =
      Eval.evaluate_with_holes
        ~eval_context:[(Id.create "input",e1);(Id.create "output",e2)]
        e
    in
    Value.equal vres Value.true_

    (*let desired_term =
      C.EasyTerm.
        (to_term
           (VSwitch
              (["O"; "S"]
              ,[(TD
                   (2,0,
                    Var))
               ;(TD
                   (2,1,
                    Var))
               ;(VSwitch
                   (["O"; "S"]
                   ,[(TD
                        (2,1,
                         Var))
                    ;(TD
                        (2,0,
                         Var))
                    ;(VC
                        ("S"
                        ,Rec
                            (TC
                               [UVD
                                  ("S"
                                  ,(TD
                                      (2,0,
                                       Var)))
                               ;UVD
                                   ("S"
                                   ,(TD
                                       (2,1,
                                        Var)))])))])
                )])
           )
        )*)

  let checker_from_equiv
      ~(problem:Problem.t)
      (e:Expr.t)
      (v1:Value.t)
      (v2:Value.t)
    : bool =
    let real_e =
      begin match Value.destruct_tuple v1 with
        | None -> Expr.mk_app e (Value.to_exp v1)
        | Some vs ->
          List.fold
            ~f:(fun acc v -> Expr.mk_app acc (Value.to_exp v))
            ~init:e
            vs
      end
    in
    let real_out = Eval.evaluate_with_holes ~eval_context:(problem.eval_context) real_e in
    Value.equal v2 real_out

  let construct_full
      ~(context:Context.t)
      ~(abstractions:AbstractionDict.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(checker:Value.t -> Value.t -> bool)
      (all_ins:Value.t list)
      (required_vs:ValueSet.t)
      (constraints:Constraints.t)
      (size:int)
    : (C.t list * ValToC.t) =
    let checker v1 v2 =
      let s = Constraints.lookup_default constraints v1 in
      begin match s with
        | StandardConstraint -> checker v1 v2
        | AddedConstraint v ->
          Value.equal v2 v
      end
    in
    (*print_endline (string_of_list Value.show all_ins);*)
    (*print_endline @$ Expr.show (C.term_to_exp_internals desired_term);
      print_endline @$ string_of_int @$ Expr.size (C.term_to_exp_internals desired_term);*)
    let inmap =
      List.fold
        ~f:(fun inmap v ->
            let abstraction =
              AbstractionDict.lookup
                abstractions
                v
            in
            let res =
              construct_single_fta
                ~abstraction
                ~context
                ~tin
                ~tout
                (fun v ->
                   let c = ValToC.lookup_exn inmap v in
                   C.get_final_values c v)
                v
                checker
                size
            in
            (*print_endline "\n";
            print_endline (Value.show v);
              print_endline (string_of_bool (C.accepts_term res desired_term));*)
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
    (*if (ValueSet.size required_vs = 2) then*)
    (*List.iter
      ~f:(fun v ->
          print_endline "Value:";
          print_endline (Value.show v);
          print_endline "C:";
          print_endline (C.show (ValToC.lookup_exn inmap v)))
      (ValueSet.as_list required_vs);*)
    (*let c =
      fold_on_head_exn
        ~f:(fun x y ->
            let inted = (C.intersect x y) in
            C.minimize inted)
        cs
      in*)
    (*print_endline (string_of_bool @$ C.accepts_term c desired_term);*)
    (cs,inmap)

  let extract_recursive_requirements
      (sin:FTAConstructor.State.t)
      (sout:FTAConstructor.State.t)
      (io:int option)
    : (Value.t * Value.t * int option) list =
    begin match (FTAConstructor.State.destruct_vals sin,FTAConstructor.State.destruct_vals sout) with
      | (Some (vvsin,_), Some (vvsout,_)) ->
        let ins = List.map ~f:snd vvsin in
        let outs = List.map ~f:snd vvsout in
        let inouts = List.zip_exn ins outs in
        List.map ~f:(fun (vsin,vsout) -> (vsin,vsout,io)) inouts
      | (None, None) ->
        []
      | _ -> failwith "when would this happen?"
    end

  let get_all_sorted_inputs_of_same_type
      (context:Context.t)
      (ds:C.TypeDS.t)
      (inputs:Value.t list)
    =
      let break = (fun v ->
          let t =
            Typecheck.typecheck_value
              context.ec
              context.tc
              context.vc
              v
          in
          C.TypeDS.is_recursive_type
            ds
            t)
      in
    let all_inputs =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map
           ~f:(subvalues_full_of_same_type
               ~context
               ~break)
           inputs)
      in
    (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
     then v1 comes before v2 in terms of generating their FTAs. This is
      necessrary for ensuring that recursion is appropriately added *)
      let sorted_inputs =
        safe_sort
        ~compare:(fun v1 v2 ->
            if Value.strict_functional_subvalue
                ~break v1 v2 then
              Some (-1)
            else if Value.strict_functional_subvalue ~break v2 v1 then
              Some 1
            else
              None)
        all_inputs
      in
      sorted_inputs

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

  let rec extract_recursive_calls
      (c:C.t)
      (ts:A.TermState.t)
    : (FTAConstructor.State.t * FTAConstructor.State.t) list =
    begin match ts with
      | TS (t,target,[source_ts]) ->
        if FTAConstructor.Transition.equal t (C.rec_ c) then
          (A.TermState.get_state source_ts,target)::(extract_recursive_calls c source_ts)
        else
          List.concat_map
            ~f:(extract_recursive_calls c)
            [source_ts]
      | TS (_,_,tss) ->
        List.concat_map
          ~f:(extract_recursive_calls c)
          tss
    end

  module PQE = struct
    module Priority = IntModule

    type t =
      {
        inputs       : ValueSet.t     ;
        c            : C.t            ;
        to_intersect : C.t list       ;
        constraints  : Constraints.t  ;
        nonpermitted : StatePairSet.t ;
        rep          : A.TermState.t  ;
        v_to_c       : ValToC.t       ;
      }
    [@@deriving eq, hash, ord, show, make]

    let make_internal
        ~(inputs:ValueSet.t)
        ~(c:C.t)
        ~(to_intersect:C.t list)
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
              to_intersect ;
            })
        rep_o

    let intersect
        (pqe:t)
      : t option option =
      let min_unsat =
        extract_min_where
          ~f:(fun cand ->
              let max_tso = C.min_term_state pqe.c in
              begin match max_tso with
                | None -> true
                | Some ts ->
                  let t = A.TermState.to_term ts in
                  not (C.accepts_term cand t)
              end)
          ~compare:C.size_compare
          pqe.to_intersect
      in
      begin match min_unsat with
        | None -> None
        | Some (min,to_intersect) ->
          (*print_endline "intersect start";*)
          let c = C.intersect min pqe.c in
          Consts.log (fun _ -> "Now intersecting: " ^ (Value.show (List.hd_exn (List.hd_exn (c.inputs)))));
          let c = C.minimize c in
          (*print_endline "intersect end";*)
          let inputs = pqe.inputs in
          let constraints = pqe.constraints in
          let nonpermitted = pqe.nonpermitted in
          let v_to_c = pqe.v_to_c in
          Some
            (make_internal
               ~inputs
               ~c
               ~to_intersect
               ~constraints
               ~nonpermitted
               ~v_to_c)
      end

    let make
        ~(inputs:ValueSet.t)
        ~(cs:C.t list)
        ~(constraints:Constraints.t)
        ~(nonpermitted:StatePairSet.t)
        ~(v_to_c:ValToC.t)
      : t option =
      let (c,to_intersect) =
        extract_min_exn
          ~compare:C.size_compare
          cs
      in
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
              to_intersect ;
            })
        rep_o

    let update_nonpermitted
        (qe:t)
        ((s1,s2,io):FTAConstructor.State.t * FTAConstructor.State.t * (int option))
      : t option =
      let (c,to_intersect) =
        begin match io with
          | None ->
            let c = C.copy qe.c in
            C.remove_transition
              c
              (C.rec_ c)
              [s1]
              s2;
            (c,qe.to_intersect)
          | Some i ->
            let (h,t) = extract_nth_exn i qe.to_intersect in
            let h = C.copy h in
            C.remove_transition
              h
              (C.rec_ qe.c)
              [s1]
              s2;
            (qe.c,h::t)
        end
      in
      let nonpermitted =
        StatePairSet.insert
          (s1,s2)
          qe.nonpermitted
      in
      make_internal
        ~inputs:qe.inputs
        ~c
        ~to_intersect:to_intersect
        ~constraints:qe.constraints
        ~nonpermitted
        ~v_to_c:qe.v_to_c

    let priority
        (qe:t)
      : int =
      (Expr.size (C.term_to_exp_internals (A.TermState.to_term qe.rep)))

    let to_string_legible
        (qe:t)
      : string =
      let es = Expr.show (C.term_to_exp_internals (A.TermState.to_term qe.rep)) in
      let cs = Constraints.show qe.constraints in
      "term: " ^ es ^ "\nconstraints: " ^ cs

    let extract_recursive_calls
        (qe:t)
        (ts:A.TermState.t)
      : (FTAConstructor.State.t * FTAConstructor.State.t * int option) list =
      let t = A.TermState.to_term ts in
      List.concat_mapi
        ~f:(fun i c ->
            List.map
              ~f:(fun (s1,s2) -> (s1,s2,Some i))
              (extract_recursive_calls
                c
                 (Option.value_exn
                    (A.accepting_term_state
                       c.a
                       t))))
        qe.to_intersect
  end

  module PQ = PriorityQueueOf(PQE)

  let safely_restricts_in_c
      (c:C.t)
      (inchoice:Value.t)
      (restriction:Value.t)
    : bool option =
    (*None means unsafe restriction, Some true means restricts outputs, false means no restricts outputs*)
    let vouts = C.get_final_values c inchoice in
    let vouts = List.dedup_and_sort ~compare:Value.compare vouts in
    if List.mem ~equal:Value.equal vouts restriction then
      Some (List.length vouts = 1)
    else
      (None)

  let safely_restricts_outputs
        (pqe:PQE.t)
        (inset:ValueSet.t)
        (vtoc:ValToC.t)
        (inchoice:Value.t)
        (restriction:Value.t)
        (io:int option)
    : bool option =
    if ValueSet.member inset inchoice then
      begin match io with
        | None ->
          safely_restricts_in_c pqe.c inchoice restriction
        | Some i ->
          safely_restricts_in_c (List.nth_exn pqe.to_intersect i) inchoice restriction
      end
    else
      safely_restricts_in_c
        (ValToC.lookup_exn vtoc inchoice)
        inchoice
        restriction

  let term_of_type t =
    let rec of_type t =
      C.EasyTerm.(
        let orig_t = t in
        begin match Type.node t with
          | Named i -> None
          | Arrow (t1,t2) -> None
          | Tuple ts ->
            let eso = List.map ~f:of_type ts in
            begin match distribute_option eso with
              | None -> None
              | Some es -> Some (orig_t,TC es)
            end
          | Mu (_,t) ->
            of_type t
          | Variant branches ->
            List.fold
              ~f:(fun acco (i,t) ->
                  begin match acco with
                    | None ->
                      let eo = of_type t in
                      Option.map ~f:(fun e -> (orig_t,VC (Id.to_string i,e))) eo
                    | Some e -> Some e
                  end)
              ~init:None
              branches
        end)
    in
    Option.map ~f:C.EasyTerm.to_term (of_type t)

  let synthesize
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(inputs:Value.t list)
      ~(pred:Value.t -> Value.t -> bool)
      ~(size:int)
      ~(abstractions:AbstractionDict.t)
    : (A.Term.t , Abstraction.t) either option =
    if (List.length inputs = 0) then
        (*Expr.of_type
           (Type.mk_arrow
              (Typecheck.concretify context.tc tin)
              (Typecheck.concretify context.tc tout))*)
      Option.map ~f:(fun e -> Left e) (term_of_type tout)
    else
      let break = (fun v ->
          let t =
            Typecheck.typecheck_value
              context.ec
              context.tc
              context.vc
              v
          in
          C.TypeDS.is_recursive_type
            ds
            t)
      in
    let all_inputs =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map
           ~f:(subvalues_full_of_same_type
               ~context
               ~break)
           inputs)
      in
    (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
     then v1 comes before v2 in terms of generating their FTAs. This is
      necessrary for ensuring that recursion is appropriately added *)
      let sorted_inputs =
        safe_sort
        ~compare:(fun v1 v2 ->
            if Value.strict_functional_subvalue
                ~break v1 v2 then
              Some (-1)
            else if Value.strict_functional_subvalue ~break v2 v1 then
              Some 1
            else
              None)
        all_inputs
    in
    let process_queue_element
        (pqe:PQE.t)
      : (PQE.t list , A.Term.t) either =
      Consts.log (fun _ -> "\n\nPopped:");
      Consts.log (fun _ -> PQE.to_string_legible pqe);
      (*print_endline (string_of_bool @$ (C.accepts_term pqe.c desired_term));*)
      begin match PQE.intersect pqe with
        | Some pqeo ->
          Left (Option.to_list pqeo)
        | None ->
          Consts.log (fun _ -> "\n\nDone Intersecting!");
          let ts = pqe.rep in
          (*print_endline @$ string_of_int @$ C.term_size @$ A.TermState.to_term ts;*)
          let rcs =
            List.dedup_and_sort
              ~compare:(triple_compare FTAConstructor.State.compare FTAConstructor.State.compare (compare_option Int.compare))
              ((*(PQE.extract_recursive_calls pqe ts)
                 @*)(List.map ~f:(fun (r1,r2) -> (r1,r2,None)) (extract_recursive_calls pqe.c ts)))
          in
          let rrs =
            List.concat_map
              ~f:(uncurry3 extract_recursive_requirements)
              rcs
          in
          let approvals =
            List.map
              ~f:(fun (v1,v2,io) ->
                  Option.map
                    ~f:(fun ro -> (ro,(v1,v2)))
                    (safely_restricts_outputs pqe pqe.inputs pqe.v_to_c v1 v2 io))
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
                let e = (*C.term_to_exp tin tout*) (A.TermState.to_term ts) in
                (*print_endline (string_of_int @$ Expr.size e);*)
                Right e
              else
                let merged_constraints_o =
                  Constraints.merge
                    pqe.constraints
                    new_constraints
                in
                begin match merged_constraints_o with
                  | None ->
                    Consts.log (fun _ -> "popped value was found impossible");
                    Left
                      (List.filter_map
                         ~f:(fun r ->
                             PQE.update_nonpermitted
                               pqe
                               r)
                         rcs)
                  | Some merged_constraints ->
                    Consts.log (fun _ -> "constraints were merged");
                    Consts.log (fun _ -> "new constraints: ");
                    Consts.log
                      (fun _ ->
                         List.to_string
                           ~f:(string_of_pair Value.show Value.show)
                           new_constraints);
                    Consts.log (fun _ -> "old constraints: ");
                    Consts.log
                      (fun _ ->
                         Constraints.show
                           pqe.constraints);
                    Consts.log (fun _ -> "inputs");
                    Consts.log (fun _ -> ValueSet.show pqe.inputs);
                    let inputs =
                      ValueSet.insert_all
                        pqe.inputs
                        (List.map ~f:fst new_constraints)
                    in
                    let (cs,v_to_c) =
                      construct_full
                        ~abstractions
                        ~context
                        ~tin
                        ~tout
                        ~checker:pred
                        sorted_inputs
                        inputs
                        merged_constraints
                        size
                    in
                    let qe =
                      PQE.make
                        ~inputs
                        ~cs
                        ~constraints:merged_constraints
                        ~nonpermitted:StatePairSet.empty
                        ~v_to_c
                    in
                    begin match qe with
                      | Some qe -> Left (qe::(List.filter_map
                                                ~f:(fun r ->
                                                    PQE.update_nonpermitted
                                                      pqe
                                                      r)
                                                rcs))
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
      end
    in
    let rec find_it_out
        (specs:PQ.t)
      : A.Term.t option =
      begin match PQ.pop specs with
        | Some (pqe,_,specs) ->
          begin match process_queue_element pqe with
            | Left new_qes ->
              find_it_out (PQ.push_all specs new_qes)
            | Right e -> Some e
          end
        | None -> None
      end
    in
    let inputs = ValueSet.from_list inputs in
    let (cs,v_to_c) =
      construct_full
        ~abstractions
        ~context
        ~tin
        ~tout
        ~checker:pred
        sorted_inputs
        inputs
        Constraints.empty
        size
    in
    let qe =
      PQE.make
        ~inputs
        ~cs
        ~constraints:Constraints.empty
        ~nonpermitted:StatePairSet.empty
        ~v_to_c
    in
    Option.map ~f:(fun e -> Left e) (find_it_out (PQ.from_list (Option.to_list qe)))

  let term_and_input_to_output
      (context:Context.t)
      (tin:Type.t)
      (input:Value.t)
      (ios:(Value.t * Value.t) list)
      (cand:A.Term.t)
    : Value.t =
    let cand_e = C.term_to_angelic_exp tin cand in
    let input = AngelicEval.from_value input in
    let ios =
      List.map
        ~f:(fun (i,o) -> (AngelicEval.from_value i, AngelicEval.from_value o))
        ios
    in
    let eval_context =
      (Id.create "x",AngelicEval.value_to_exp input)
      ::(List.map ~f:(fun (i,v) -> (i,AngelicEval.from_exp v)) context.evals)
    in
    let (_,output) =
      AngelicEval.evaluate_with_holes
        ~eval_context
        ios
        (AngelicEval.App (cand_e,AngelicEval.value_to_exp input))
    in
    AngelicEval.to_value output

  let abstract_node
      (context:Context.t)
      (ins:A.Term.t list)
      (input:Value.t)
      (ios:(Value.t * Value.t) list)
      (tin:Type.t)
      (conversion:Value.t list -> Value.t)
      (pred:Value.t -> bool)
    : (A.Term.t * Predicate.t) list =
    let invs = List.map ~f:(fun t -> (t,term_and_input_to_output context tin input ios t)) ins in
    let out = conversion (List.map ~f:snd invs) in
    invs

  let abstract_all_in_example
    (context:Context.t)
      (input:Value.t)
      (ios:(Value.t * Value.t) list)
      (tin:Type.t)
      (Term (tr,_) as t:A.Term.t)
    : (Value.t list) * ((Type.t * Predicate.t) list) =
    let eval_context =
      (Id.create "x",AngelicEval.from_exp (Value.to_exp input))
      ::(List.map ~f:(fun (i,v) -> (i,AngelicEval.from_exp v)) context.evals)
    in
    let angelic_ios = List.map ~f:(fun (v1,v2) -> (AngelicEval.from_value v1, AngelicEval.from_value v2)) ios in
    let rec process_qes
        (acc:((Type.t * Predicate.t) list))
        (qns:(A.Term.t list * (Value.t list -> Value.t) * (Value.t -> bool)) list)
      : ((Type.t * Predicate.t) list) =
      begin match qns with
        | [] -> acc
        | h::qns ->
          let (ins,conversion,pred) = h in
          let ps = abstract_node context ins input ios tin conversion pred in
          let acc = (List.map ~f:(fun (Term (tr,_),p) -> (FTAConstructor.Transition.get_type tr,p)) ps)@acc in
          let new_qns =
            List.map
              ~f:(fun (Term (tr,ts),p) ->
                  let v_trans vs =
                    let vs_as_es = List.map ~f:(AngelicEval.from_exp % Value.to_exp) vs in
                    let to_expr = FTAConstructor.Transition.to_expr tr vs_as_es in
                    let (_,v) =
                      AngelicEval.evaluate_with_holes
                        ~eval_context
                        angelic_ios
                        to_expr
                    in
                    AngelicEval.to_value v
                  in
                  (ts,v_trans,(fun v -> Predicate.(=>) v p))
                )
              ps
          in
          process_qes acc (new_qns@qns)
      end
    in
    ([],process_qes [] [([t],List.hd_exn,(fun _ -> true))])


  let ensure_and_refine
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(cand:A.Term.t)
      ~(inputs:Value.t list)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(pred:Value.t -> Value.t -> bool)
    : (Value.t * Type.t * Predicate.t) list =
    let cand_e = C.term_to_angelic_exp tin cand in
    let all_sorted_inputs =
      get_all_sorted_inputs_of_same_type context ds inputs
    in
    let all_sorted_ios =
      List.fold
        ~f:(fun ios inv ->
            let inv = AngelicEval.from_value inv in
            let (_,outv) =
              AngelicEval.evaluate_with_holes
                ~eval_context:(List.map ~f:(fun (i,e) -> (i,AngelicEval.from_exp e)) context.evals)
                ios
                (AngelicEval.App (cand_e,AngelicEval.value_to_exp inv))
            in
            (inv,outv)::ios)
        ~init:[]
        all_sorted_inputs
    in
    let ios =
      List.map
        ~f:(fun (inv,outv) -> (AngelicEval.to_value inv,AngelicEval.to_value outv))
        all_sorted_ios
    in
    let bads =
      List.filter_map
        ~f:(fun inv ->
            let outv =
              AngelicEval.to_value
                (List.Assoc.find_exn
                   ~equal:AngelicEval.equal_value
                   all_sorted_ios
                   (AngelicEval.from_value inv))
            in
            if pred inv outv then
              None
            else
              Some (inv,outv))
        inputs
    in
    List.concat_map
      ~f:(fun (vin,out) ->
          let (_,tps) =
            abstract_all_in_example
              context
              vin
              ios
              tin
              cand
          in
          List.map ~f:(fun (t,p) -> (vin,t,p)) tps)
      bads

  let rec synthesize_abstraction
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(pred:Value.t -> Value.t -> bool)
      ~(inputs:Value.t list)
      ~(size:int)
      ~(abstractions:AbstractionDict.t)
    : (Expr.t , AbstractionDict.t) either =
    print_endline @$ AbstractionDict.show abstractions;
    let eo =
      synthesize
        ~context
        ~tin
        ~tout
        ~inputs
        ~pred
        ~size
        ~abstractions
        ~ds
    in
    begin match eo with
      | None -> Right abstractions
      | Some (Right abstractions) -> failwith "ah"
      | Some (Left cand) ->
        begin match ensure_and_refine ~cand ~ds ~context ~inputs ~pred ~tin ~tout with
          | [] ->
            (Left (C.term_to_exp tin tout cand))
          | refinement ->
            let abstractions =
              AbstractionDict.integrate_refinement
                abstractions
                refinement
            in
            synthesize_abstraction
              ~ds
              ~context
              ~tin
              ~tout
              ~inputs
              ~pred
              ~size
              ~abstractions
        end
    end

  let rec synthesize_caller
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(pred:Value.t -> Value.t -> bool)
      ~(inputs:Value.t list)
      ~(size:int)
      ~(abstractions:AbstractionDict.t)
    : Expr.t =
    Consts.log (fun _ -> "Synthesis started with size " ^ (string_of_int size));
    let e_or_a =
      synthesize_abstraction
        ~ds
        ~context
        ~tin
        ~tout
        ~inputs
        ~pred
        ~size
        ~abstractions
    in
    begin match e_or_a with
      | Right abstractions ->
        failwith "end early"
        (*synthesize_caller
          ~ds
          ~context
          ~tin
          ~tout
          ~pred
          ~inputs
          ~size:(size+1)
          ~abstractions*)
      | Left e ->
        e
    end

  let synth
      (a:t)
      (inputs:Value.t list)
      (pred:Value.t -> Value.t -> bool)
    : t * Expr.t =
    let context = (context a) in
    let tin = tin a in
    let tout = tout a in
    let all_ins =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map ~f:Value.subvalues inputs) (*TODO*)
    in
    let ts =
      ([tin;tout]
       @(List.map ~f:Type.mk_named (Context.keys context.tc))
       @(Context.data context.ec)
       @(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) all_ins))
    in
    let ds =
      C.create_ds_from_t_list_context
        ~context
        ts
    in
    Consts.log (fun () -> "inputs: " ^ (string_of_list Value.show inputs));
    (a,synthesize_caller
      ~context
      ~tin
      ~tout
      ~inputs
      ~pred
      ~ds
      ~size:2
      ~abstractions:AbstractionDict.empty)
end
