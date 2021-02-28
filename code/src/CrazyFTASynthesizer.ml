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
      Consts.initial_creation_times
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
                 if Predicate.implied_by_strict_functional_subvalue ~break v1 input then
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
                   let vc = ValToC.as_kvp_list inmap in
                   let all_valids = List.filter ~f:(fun (v',_) -> Predicate.(=>) v' v) vc in
                   List.concat_map ~f:(fun (v,c) -> C.get_final_values c v) all_valids)
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
      (sin:A.TermState.t)
      (sout:FTAConstructor.State.t)
      (io:int option)
    : (Value.t * Value.t * Value.t * int option * A.Term.t) list =
    begin match ((A.TermState.get_state sin),sout) with
      | ((vvsin,_), (vvsout,_)) ->
        let t = A.TermState.to_term sin in
        let outs = List.map ~f:snd vvsout in
        let inouts = List.zip_exn vvsin outs in
        List.filter_map
          ~f:(fun ((exv,vsino),vsouto) ->
              begin match (vsino,vsouto) with
                | (Some vsin, Some vsout) ->
                  Some (exv,vsin,vsout,io,t)
                | _ ->
                  None
              end)
          inouts
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
    : (A.TermState.t * FTAConstructor.State.t) list =
    begin match ts with
      | TS (t,target,[source_ts]) ->
        if FTAConstructor.Transition.equal t (C.rec_ c) then
          (source_ts,target)::(extract_recursive_calls c source_ts)
        else
          List.concat_map
            ~f:(extract_recursive_calls c)
            [source_ts]
      | TS (_,_,tss) ->
        (*TODO: no rec calls on unprocessed branches*)
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
          Consts.log (fun _ -> "Now intersecting: " ^ (Value.show (List.hd_exn (List.hd_exn (min.inputs)))));
          let c = C.intersect min pqe.c in
          Consts.log (fun _ -> "Now minimizing: " ^ (Value.show (List.hd_exn (List.hd_exn (c.inputs)))));
          let c = C.minimize c in
          Consts.log (fun _ -> string_of_float (Consts.max Consts.isect_times));
          (*print_endline (string_of_int (A.size c.a));*)
          (*print_endline "intersect end";*)
          let inputs = pqe.inputs in
          (*let pairs =
            C.get_all_state_pairs
              c
          in
          List.iter
            ~f:(fun vs -> print_endline (string_of_list Value.show vs))
            pairs;*)
          (*print_endline "CStatesAre";
          List.iter
            ~f:(fun s -> print_endline (FTAConstructor.State.show s))
            (A.states c.a);
            print_endline "CStatesEnd";*)
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
        ((s1,s2,io):A.TermState.t * FTAConstructor.State.t * (int option))
      : t option =
      let (c,to_intersect) =
        begin match io with
          | None ->
            let c = C.copy qe.c in
            C.remove_transition
              c
              (C.rec_ c)
              [A.TermState.get_state s1]
              s2;
            (c,qe.to_intersect)
          | Some i ->
            let (h,t) = extract_nth_exn i qe.to_intersect in
            let h = C.copy h in
            C.remove_transition
              h
              (C.rec_ qe.c)
              [A.TermState.get_state s1]
              s2;
            (qe.c,h::t)
        end
      in
      let nonpermitted =
        StatePairSet.insert
          (A.TermState.get_state s1,s2)
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
              ~f:(fun (s1,s2) -> (A.TermState.get_state s1,s2,Some i))
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

  type qe_ret =
    | NewQEs of PQE.t list
    | FoundResult of A.Term.t
    | AbstractionNeeded of A.Term.t * ((Value.t * A.Term.t) list)

  let synthesize
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(inputs:Value.t list)
      ~(pred:Value.t -> Value.t -> bool)
      ~(size:int)
      ~(abstractions:AbstractionDict.t)
    : (A.Term.t , A.Term.t * ((Value.t * A.Term.t) list)) either option =
    if (List.length inputs = 0) then
        (*Expr.of_type
           (Type.mk_arrow
              (Typecheck.concretify context.tc tin)
              (Typecheck.concretify context.tc tout))*)
      Some (Left (C.term_of_type_exn ds tout))
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
      : qe_ret =
      Consts.log (fun _ -> "\n\nPopped:");
      Consts.log (fun _ -> PQE.to_string_legible pqe);
      (*print_endline (string_of_bool @$ (C.accepts_term pqe.c desired_term));*)
      begin match PQE.intersect pqe with
        | Some pqeo ->
          NewQEs (Option.to_list pqeo)
        | None ->
          Consts.log (fun _ -> "\n\nDone Intersecting!");
          let ts = pqe.rep in
          (*print_endline @$ string_of_int @$ C.term_size @$ A.TermState.to_term ts;*)
          let rcs =
            List.dedup_and_sort
              ~compare:(triple_compare A.TermState.compare FTAConstructor.State.compare (compare_option Int.compare))
              ((*(PQE.extract_recursive_calls pqe ts)
                 @*)(List.map ~f:(fun (r1,r2) -> (r1,r2,None)) (extract_recursive_calls pqe.c ts)))
          in
          let rrs =
            List.concat_map
              ~f:(uncurry3 extract_recursive_requirements)
              rcs
          in
          begin match List.filter ~f:(fun (_,v,_,_,_) -> not (Predicate.is_concrete v)) rrs with
            | [] ->
              let approvals =
                List.map
                  ~f:(fun (_,v1,v2,io,_) ->
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
                    FoundResult e
                  else
                    let merged_constraints_o =
                      Constraints.merge
                        pqe.constraints
                        new_constraints
                    in
                    (*print_endline "here2";*)
                    begin match merged_constraints_o with
                      | None ->
                        Consts.log (fun _ -> "popped value was found impossible");
                        NewQEs
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
                          | Some qe -> NewQEs (qe::(List.filter_map
                                                      ~f:(fun r ->
                                                          PQE.update_nonpermitted
                                                            pqe
                                                            r)
                                                      rcs))
                          | None ->
                            Consts.log (fun _ -> "popped value was found impossible");
                            NewQEs
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
                  NewQEs
                    (List.filter_map
                       ~f:(fun r ->
                           PQE.update_nonpermitted
                             pqe
                             r)
                       rcs)
              end
            | abstracts ->
              AbstractionNeeded
                (A.TermState.to_term ts,List.map ~f:(fun (inv,_,_,_,ts) -> (inv,ts)) abstracts)
          end
      end
    in
    let rec find_it_out
        (specs:PQ.t)
      : (A.Term.t , A.Term.t * ((Value.t * A.Term.t) list)) either option =
      begin match PQ.pop specs with
        | Some (pqe,_,specs) ->
          begin match process_queue_element pqe with
            | NewQEs new_qes ->
              find_it_out (PQ.push_all specs new_qes)
            | FoundResult e -> Some (Left e)
            | AbstractionNeeded (t,ts) -> Some (Right (t,ts))
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
    (find_it_out (PQ.from_list (Option.to_list qe)))

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
    try
      let (_,output) =
        AngelicEval.evaluate_with_holes
          ~eval_context
          ios
          (AngelicEval.App (cand_e,AngelicEval.value_to_exp input))
      in
      (*List.map ~f:(fun (inv,outv) -> (AngelicEval.to_value inv, AngelicEval.to_value outv)) rec_calls,AngelicEval.to_value output*)
      AngelicEval.to_value output
    with _ ->
      Value.mk_wildcard


  let abstract_node
      (context:Context.t)
      (ins:A.Term.t list)
      (input:Value.t)
      (ios:(Value.t * Value.t) list)
      (tin:Type.t)
      (conversion:Value.t list -> Value.t)
      (pred:Value.t -> bool)
    : (Value.t * (Predicate.t -> bool)) list * (A.Term.t * Predicate.t) list =
    let invs =
      List.map
        ~f:(fun t -> (t,term_and_input_to_output context tin input ios t))
        ins
    in
    let maximally_abstracted_invs : (A.Term.t * Predicate.t) list =
      List.zip_exn
        (List.map ~f:fst invs)
        (Abstraction.abstract_list
           (List.map ~f:snd invs)
           (pred % conversion))
    in
    let either_invs =
      List.concat_map
        ~f:(fun ((Term (tr,ts),p) as fullterm) ->
            begin match FTAConstructor.Transition.id tr with
              | FTAConstructor.Transition.Rec ->
                begin match ts with
                  | [subterm] ->
                    let subcall = term_and_input_to_output context tin input ios subterm in
                    if Predicate.equal p Predicate.top then
                      []
                    else
                      [Left (subcall,fun p' -> Predicate.(=>) p' p)
                      ;Right fullterm]
                  | _ -> failwith "ill formed"
                end
              | _ -> [Right fullterm]
            end)
        maximally_abstracted_invs
    in
    split_by_either either_invs
      (*TODO: this misses recursive calls *)
        (*let out = conversion (List.map ~f:snd invs) in*)

  let abstract_all_in_example
      (context:Context.t)
      (input:Value.t)
      (ios:(Value.t * Value.t) list)
      (tin:Type.t)
      (Term (tr,_) as t:A.Term.t)
      (pred:Predicate.t -> bool)
    : ((Value.t * (Predicate.t -> bool)) list) * ((Type.t * Predicate.t) list) =
    let eval_context =
      (Id.create "x",AngelicEval.from_exp (Value.to_exp input))
      ::(List.map ~f:(fun (i,v) -> (i,AngelicEval.from_exp v)) context.evals)
    in
    let angelic_ios = List.map ~f:(fun (v1,v2) -> (AngelicEval.from_value v1, AngelicEval.from_value v2)) ios in
    let rec process_qes
        ((rcacc,tpacc) as acc:((Value.t * (Predicate.t -> bool)) list) * ((Type.t * Predicate.t) list))
        (qns:(A.Term.t list * (Value.t list -> Value.t) * (Predicate.t -> bool)) list)
      : ((Value.t * (Predicate.t -> bool)) list) * ((Type.t * Predicate.t) list) =
      begin match qns with
        | [] -> acc
        | h::qns ->
          let (ins,conversion,pred) = h in
          let (rcs,ps) = abstract_node context ins input ios tin conversion pred in
          let tpacc = (List.map ~f:(fun (Term (tr,_),p) -> (FTAConstructor.Transition.get_type tr,p)) ps)@tpacc in
          let rcacc = rcs@rcacc in
          let new_qns =
            List.map
              ~f:(fun (Term (tr,ts),p) ->
                  let v_trans vs =
                    let vs_as_es = List.map ~f:(AngelicEval.from_exp % Value.to_exp) vs in
                    let to_expr = FTAConstructor.Transition.to_expr tr vs_as_es in
                    try
                      let (_,v) =
                        AngelicEval.evaluate_with_holes
                          ~eval_context
                          angelic_ios
                          to_expr
                      in
                      AngelicEval.to_value v
                    with _ ->
                      Predicate.top
                  in
                  (ts,v_trans,(fun v -> Predicate.(=>) v p))
                )
              ps
          in
          process_qes (rcacc,tpacc) (new_qns@qns)
      end
    in
    process_qes ([],[]) [([t],List.hd_exn,pred)]

  let abstract_all_full_example
      (context:Context.t)
      (input:Value.t)
      (ios:(Value.t * Value.t) list)
      (tin:Type.t)
      (t:A.Term.t)
      (pred:Predicate.t -> bool)
    : (Value.t * Type.t * Predicate.t) list =
    let rec aafe_rec
        (acc:(Value.t * Type.t * Predicate.t) list)
        (qes:(Value.t * (Predicate.t -> bool)) list)
      : (Value.t * Type.t * Predicate.t) list =
      begin match qes with
        | [] -> acc
        | (input,p)::qes ->
          (*print_endline (Value.show input);*)
          let (new_qes,new_accs) = abstract_all_in_example context input ios tin t p in
          let new_accs = List.map ~f:(fun (t,p) -> (input,t,p)) new_accs in
          aafe_rec (new_accs@acc) (new_qes@qes)
      end
    in
    (*let output = List.Assoc.find_exn ~equal:Value.equal ios input in*)
    aafe_rec
      []
      [(input,pred)]

  let force_refine
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(cand:A.Term.t)
      ~(relevant_terms:(Value.t * A.Term.t) list)
      ~(tin:Type.t)
      ~(tout:Type.t)
    : (Value.t * Type.t * Predicate.t) list =
    let cand_e = C.term_to_angelic_exp tin cand in
    (*print_endline (Expr.show (C.term_to_exp_internals cand));*)
    (*List.iter
      ~f:(fun (i,e) ->
          print_endline (Id.show e);
          print_endline (A.Term.show i)
        )
      (C.extract_unbranched_switches cand);
    print_endline (A.Term.show cand);
    print_endline (Expr.show (C.term_to_exp tin tout cand));
      assert (List.length (C.extract_unbranched_switches cand) = 0);*)
    let all_sorted_inputs =
      get_all_sorted_inputs_of_same_type context ds (List.map ~f:fst relevant_terms)
    in
    let all_sorted_ios =
      List.fold
        ~f:(fun ios inv ->
            let inv = AngelicEval.from_value inv in
            try
              let (_,outv) =
                AngelicEval.evaluate_with_holes
                  ~eval_context:(List.map ~f:(fun (i,e) -> (i,AngelicEval.from_exp e)) context.evals)
                  ios
                  (AngelicEval.App (cand_e,AngelicEval.value_to_exp inv))
              in
              (inv,outv)::ios
            with _ ->
              ios)
        ~init:[]
        all_sorted_inputs
    in
    let ios =
      List.map
        ~f:(fun (inv,outv) -> (AngelicEval.to_value inv,AngelicEval.to_value outv))
        all_sorted_ios
    in
    List.concat_map
      ~f:(fun (vin,term) ->
          let tps =
            abstract_all_full_example
              context
              vin
              ios
              tin
              term
              Predicate.is_concrete
          in
          tps
          (*List.map ~f:(fun (t,p) -> (vin,t,p)) tps*))
      relevant_terms

  let ensure_and_refine
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(cand:A.Term.t)
      ~(inputs:Value.t list)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(pred:Value.t -> Predicate.t -> bool)
    : (Value.t * Type.t * Predicate.t) list =
    let cand_e = C.term_to_angelic_exp tin cand in
    (*print_endline (Expr.show (C.term_to_exp_internals cand));*)
    (*List.iter
      ~f:(fun (i,e) ->
          print_endline (Id.show e);
          print_endline (A.Term.show i)
        )
      (C.extract_unbranched_switches cand);
    print_endline (A.Term.show cand);
    print_endline (Expr.show (C.term_to_exp tin tout cand));
      assert (List.length (C.extract_unbranched_switches cand) = 0);*)
    let all_sorted_inputs =
      get_all_sorted_inputs_of_same_type context ds inputs
    in
    let all_sorted_ios =
      List.fold
        ~f:(fun ios inv ->
            let inv = AngelicEval.from_value inv in
            try
              let (_,outv) =
                AngelicEval.evaluate_with_holes
                  ~eval_context:(List.map ~f:(fun (i,e) -> (i,AngelicEval.from_exp e)) context.evals)
                  ios
                  (AngelicEval.App (cand_e,AngelicEval.value_to_exp inv))
              in
              (inv,outv)::ios
            with _ ->
              ios)
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
            (*print_endline (Value.show inv);*)
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
          let tps =
            abstract_all_full_example
              context
              vin
              ios
              tin
              cand
              (fun p -> not (pred vin p))
          in
          tps
          (*List.map ~f:(fun (t,p) -> (vin,t,p)) tps*))
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
      | Some (Right (t,ts)) ->
        let t = C.ensure_switches ds context t tout in
        let refinement =
          force_refine
            ~context
            ~ds
            ~cand:t
            ~relevant_terms:ts
            ~tin
            ~tout
        in
        Consts.log
          (fun _ -> "Forced New Refinements: "
                    ^ (string_of_list (string_of_triple Value.show Type.show Predicate.show)
                         (List.filter
                            ~f:(fun (v,t,p) ->
                                not @$
                                Predicate.equal
                                  (Abstraction.abstract
                                     (AbstractionDict.lookup abstractions v)
                                     p
                                     t)
                                  p)
                            refinement
                         )));
        let abstractions =
          AbstractionDict.integrate_refinement
            abstractions
            refinement
        in
        Consts.log (fun _ -> "Full Abstraction: " ^ AbstractionDict.show abstractions);
        synthesize_abstraction
          ~ds
          ~context
          ~tin
          ~tout
          ~inputs
          ~pred
          ~size
          ~abstractions
      | Some (Left cand) ->
        let cand = C.ensure_switches ds context cand tout in
        begin match ensure_and_refine ~cand ~ds ~context ~inputs ~pred ~tin ~tout with
          | [] ->
            (Left (C.term_to_exp tin tout cand))
          | refinement ->
            Consts.log
              (fun _ -> "Unenforced New Refinements: "
                        ^ (string_of_list (string_of_triple Value.show Type.show Predicate.show)
                             (List.filter
                                ~f:(fun (v,t,p) ->
                                    not @$
                                    Predicate.equal
                                      (Abstraction.abstract
                                         (AbstractionDict.lookup abstractions v)
                                         p
                                         t)
                                      p)
                                refinement
                             )));
            let abstractions =
              AbstractionDict.integrate_refinement
                abstractions
                refinement
            in
            Consts.log (fun _ -> "Full Abstraction: " ^ AbstractionDict.show abstractions);
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
        synthesize_caller
          ~ds
          ~context
          ~tin
          ~tout
          ~pred
          ~inputs
          ~size:(size+1)
          ~abstractions
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
