open MyStdLib
open Lang

module Create(B : Automata.AutomatonBuilder) (*: Synthesizers.PredicateSynth.S *)= struct
  module A = B(FTAConstructor.Transition)(FTAConstructor.State)
  module C = FTAConstructor.Make(A)

  let __INITIAL_SIZE__ = 2
  let __INITIAL_MVM__ = 3.0

  module ValToC = DictOf(Value)(C)
  module ValueSet = SetOf(Value)
  module IndividualSettings = struct
    type t =
      {
        max_value_multiplier : Float.t ;
      }
    [@@deriving eq, hash, ord, show]

    let initial =
      {
        max_value_multiplier = __INITIAL_MVM__ ;
      }

    let increase_mvm is =
      {
        max_value_multiplier = is.max_value_multiplier +. 1.0 ;
      }
  end

  module GlobalState = struct
    module D = DictOf(Value)(IndividualSettings)
    type t =
      {
        d : D.t ;
        size : int ;
        kb : KnowledgeBase.t ;
      }
    [@@deriving eq, hash, ord, show]

    let empty : t =
      {
        d = D.empty ;
        size = __INITIAL_SIZE__ ;
        kb = KnowledgeBase.empty
      }

    let lookup
        (gs:t)
        (v:Value.t)
      : IndividualSettings.t =
      begin match D.lookup gs.d v with
        | None -> IndividualSettings.initial
        | Some is -> is
      end

    let upgrade_from_failed_isect
        (gs:t)
      : t =
      { gs with size = gs.size+1; kb = KnowledgeBase.empty }

    let upgrade_kb
        (gs:t)
        (nppfc:KnowledgeBase.NPPFConj.t)
      : t =
      { gs with kb = KnowledgeBase.add gs.kb nppfc }

    let get_kb
        (gs:t)
      : KnowledgeBase.t =
      gs.kb

    let increase_max_multiplier
        (gs:t)
        (v:Value.t)
      : t =
      let is = lookup gs v in
      let is = IndividualSettings.increase_mvm is in
      { gs with
        d = D.insert gs.d v is
      }

    let get_num_applications
        (gs:t)
      : int =
      gs.size

    let get_max_value_multiplier
        (s:t)
        (v:Value.t)
      : Float.t =
      let is = lookup s v in
      is.max_value_multiplier
  end

  let strict_functional_subvalue
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      (v1:Value.t)
      (v2:Value.t)
    : bool =
    let break = fun v ->
      let t =
        Typecheck.typecheck_value
          context.ec
          context.tc
          context.vc
          v
      in
      C.TypeDS.is_recursive_type
        ds
        t
    in
    Value.strict_functional_subvalue ~break v1 v2

  let subvalues_full_of_same_type
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      (v:Value.t)
    : Value.t list =
    let break = fun v ->
      let t =
        Typecheck.typecheck_value
          context.ec
          context.tc
          context.vc
          v
      in
      C.TypeDS.is_recursive_type
        ds
        t
    in
    let t = Typecheck.typecheck_value context.ec context.tc context.vc v in
    let subvalues_full = Value.functional_subvalues ~break v in
    List.filter
      ~f:(fun v ->
          Typecheck.type_equiv
            context.tc
            (Typecheck.typecheck_value context.ec context.tc context.vc v)
            t)
      subvalues_full

  type single_fta_response =
    | Generated of C.t
    | IncreaseMaxResponse

  let rec construct_single_fta
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(gs:GlobalState.t)
      (sub_calls:Value.t -> Value.t list)
      (input:Value.t)
      (valid_ios:Value.t -> Value.t -> bool)
    : C.t * GlobalState.t =
    let mvm = GlobalState.get_max_value_multiplier gs input in
    let ans_o =
      Consts.time
        Consts.initial_creation_times
        (fun _ ->
           let c =
             C.initialize_context
               ~context
               ~value_filter:((fun v' -> Value.size_min_expr v' <= Float.to_int (Float.of_int (Value.size_min_expr input)+.mvm)))
               ([tin;tout]
                @(List.map ~f:Type.mk_named (Context.keys context.tc))
                @(Context.data context.ec)
                @(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) (Value.subvalues input)))
               [input]
               (tin,tout)
               valid_ios
           in
           let rec get_all_partial_apps
               (ins:Type.t list)
               (base:Expr.t)
               (extractor:Type.t -> Expr.t list)
             : ((Type.t list * Expr.t) list) =
             let basic = (ins,base) in
             let advanced =
               begin match ins with
                 | [] -> []
                 | h::t ->
                   if Option.is_some (Type.destruct_arr h) then
                     let apps = extractor h in
                     List.concat_map
                       ~f:(fun app ->
                           let base = Expr.mk_app base app in
                           get_all_partial_apps t base extractor)
                       apps
                   else
                     []
               end
             in
             basic::advanced
           in
           let context_conversions =
             List.concat_map
               ~f:(fun (i,e) ->
                   let t = Context.find_exn context.ec i in
                   let (ins,out) = Type.split_to_arg_list_result t in
                   let possible_partials =
                     get_all_partial_apps
                       ins
                       (Expr.mk_var i)
                       (fun t ->
                          List.filter_map
                            ~f:(fun (i,_) ->
                                let t' = Context.find_exn context.ec i in
                                if Typecheck.type_equiv context.tc t t' then
                                  (Some (Expr.mk_var i))
                                else
                                  None)
                            context.evals)
                   in
                   List.concat_map
                     ~f:(fun (ins,e) ->
                         let ins =
                           List.map
                             ~f:(fun int -> (int,TermClassification.Introduction))
                             ins
                         in
                         let e_func = Expr.replace_holes ~i_e:context.evals e in
                         let e_func = Value.to_exp (Eval.evaluate e_func) in
                         let evaluation vs =
                           let es = List.map ~f:Value.to_exp vs in
                           [Eval.evaluate
                              (List.fold
                                 ~f:Expr.mk_app
                                 ~init:e_func
                                 es)]
                         in
                         [(FTAConstructor.Transition.FunctionApp e,evaluation,ins,(out,TermClassification.Elimination))
                         ;(FTAConstructor.Transition.FunctionApp e,evaluation,ins,(out,TermClassification.Introduction))])
                     possible_partials)
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
                             [(FTAConstructor.Transition.TupleDestruct (i)
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
                             ;(FTAConstructor.Transition.TupleDestruct i
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
                     begin
                       sub_calls v1
                     end
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
             variant_construct_conversions
             @ tuple_constructors
             @ eval_conversion
             @ tuple_destructors
             @ variant_unsafe_destruct_conversions
           in
           let all_conversions =
             context_conversions
             @ rec_call_conversions
             @ conversions
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
           let no_news =
             List.fold
               ~f:(fun last_adds i ->
                   begin match last_adds with
                     | None -> None
                     | Some (old_added,old_pruned) ->
                       let (d1,e1) = C.update_from_conversions c variant_unsafe_destruct_conversions in
                       let (d2,e2) = C.update_from_conversions c tuple_destructors in
                       let (d3,e3) =
                         C.update_from_conversions c conversions
                       in
                       let (d4,e4) =
                         C.update_from_conversions c all_conversions
                       in
                       let new_added = (List.length d1) + (List.length d2) + (List.length d3) + (List.length d4) in
                       let new_pruned = (List.length e1) + (List.length e2) + (List.length e3) + (List.length d4) in
                       if new_pruned > 0 &&
                          (new_added = 0 ||
                           (Float.to_int (Float.of_int new_added *. 5.0) < old_added && new_pruned > (Float.to_int (Float.of_int old_pruned *. 5.0)))) then
                         None
                       else
                         Some (new_added, new_pruned)
                   end)
               ~init:(Some (0,0))
               (range 0 (GlobalState.get_num_applications gs))
           in
           if Option.is_none no_news then
             begin
               IncreaseMaxResponse
             end
           else
             begin
               (*C.update_from_conversions c (destruct_conversions) ~ensure_state:false;*)
               C.add_destructors c;
               let c = C.minimize c in
               Generated c
             end)
    in
    begin match ans_o with
      | IncreaseMaxResponse ->
        let gs = GlobalState.increase_max_multiplier gs input in
        Consts.log
          (fun () ->
             "MVM increased on " ^
             (Value.show input) ^
             " to " ^
             (Float.to_string (GlobalState.get_max_value_multiplier gs input)));
        construct_single_fta
          ~context
          ~tin
          ~tout
          ~gs
          sub_calls
          input
          valid_ios
      | Generated ans ->
        (ans,gs)
    end

  let construct_full
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(checker:Value.t -> Value.t -> bool)
      ~(gs:GlobalState.t)
      (all_ins:Value.t list)
      (required_vs:ValueSet.t)
    : (C.t list * ValToC.t * GlobalState.t) =
    let (inmap,gs) =
      List.fold
        ~f:(fun (inmap,gs) v ->
            let (res,gs) =
              construct_single_fta
                ~context
                ~tin
                ~tout
                ~gs
                (fun v ->
                   let vc = ValToC.as_kvp_list inmap in
                   let all_valids = List.filter ~f:(fun (v',_) -> Predicate.(=>) v' v) vc in
                   List.concat_map ~f:(fun (v,c) -> C.get_final_values c v) all_valids)
                v
                checker
            in
            (ValToC.insert
               inmap
               v
               res,gs))
        ~init:(ValToC.empty,gs)
        all_ins
    in
    let cs =
      List.map
        ~f:(ValToC.lookup_exn inmap)
        (ValueSet.as_list required_vs)
    in
    (cs,inmap,gs)

  let get_all_sorted_inputs_of_same_type
      (context:Context.t)
      (ds:C.TypeDS.t)
      (inputs:Value.t list)
    =
    let all_inputs =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map
           ~f:(subvalues_full_of_same_type
                 ~context
                 ~ds)
           inputs)
    in
    (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
      then v1 comes before v2 in terms of generating their FTAs. This is
      necessrary for ensuring that recursion is appropriately added *)
    let sorted_inputs =
      safe_sort
        ~compare:(fun v1 v2 ->
            if strict_functional_subvalue ~context ~ds v1 v2 then
              Some (-1)
            else if strict_functional_subvalue ~context ~ds v2 v1 then
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

  module TermSet = SetOf(A.Term)
  let procd = ref TermSet.empty
  let subprocd = ref TermSet.empty

  let rec add_all_subterms
      (Term (_,ts) as fullt:A.Term.t)
    : unit =
    if TermSet.member !subprocd fullt then
      begin
        ()
      end
    else
      begin
        subprocd := TermSet.insert fullt !subprocd;
        List.iter
          ~f:add_all_subterms
          ts
      end


  module PQE = struct
    type t =
      {
        inputs       : ValueSet.t     ;
        c            : C.t            ;
        to_intersect : C.t list       ;
        rep          : A.TermState.t  ;
        v_to_c       : ValToC.t       ;
        new_spec     : ((Value.t list) * (Value.t list) * (Value.t -> Value.t -> bool) * C.TypeDS.t) option ;
      }
    [@@deriving show, make]

    let hash_fold_t _ _ = failwith "unimplemented"
    let hash _ = failwith "unimplemented"
    let compare _ _ = failwith "unimplemented"
    let equal _ _ = failwith "unimplemented"

    let make_internal
        ~(inputs:ValueSet.t)
        ~(c:C.t)
        ~(to_intersect:C.t list)
        ~(v_to_c:ValToC.t)
      : t option =
      let rep_o = C.min_term_state_silly c (fun t -> TermSet.member !subprocd t) (fun t -> TermSet.member !procd t) in
      begin match rep_o with
        | None ->
          None
        | Some rep ->
          Some
            {
              inputs       ;
              c            ;
              rep          ;
              v_to_c       ;
              to_intersect ;
              new_spec = None ;
            }
      end

    let extract_possible_calls
        (x:t)
        (vs:Value.t list)
      : (Value.t * Value.t list) list =
      List.map
        ~f:(fun v ->
            if List.mem ~equal:Value.equal x.c.inputs v then
              let c = x.c in
              (v,C.get_final_values c v)
            else
              let c = ValToC.lookup_exn x.v_to_c v in
              (v,C.get_final_values c v))
        vs

    let intersect
        (value_map:Value.t -> Value.t list)
        (context:Context.t)
        (ds:C.TypeDS.t)
        (pqe:t)
      : (t option) option =
      let e_o =
        Option.map
          ~f:(C.term_to_angelic_exp Type._unit % A.TermState.to_term)
          (C.min_term_state pqe.c)
      in
      (*let eval_context =
        List.map
          ~f:(fun (i,e) -> (i,AngelicEval.from_exp e))
          context.evals
        in*)
      let min_unsat =
        extract_min_where
          ~f:(fun cand ->
              begin match e_o with
                | None -> true
                | Some e ->
                  let ans = not (C.accepts_term cand (A.TermState.to_term (Option.value_exn (C.min_term_state pqe.c)))) in
                  ans
                  (*let inputs = cand.inputs in
                    let checker = cand.final_candidates in

                    not
                    (List.for_all
                       ~f:(fun input ->
                           let subvalues =
                             subvalues_full_of_same_type
                               ~context
                               ~ds
                               input
                           in
                           let subcalls =
                             List.map
                               ~f:(fun sv ->
                                   (AngelicEval.from_value sv
                                   ,List.map ~f:AngelicEval.from_value (value_map sv)))
                               subvalues
                           in
                           let outputs =
                             AngelicEval.evaluate_with_holes
                               ~eval_context
                               subcalls
                               (AngelicEval.App
                                  (e
                                  ,AngelicEval.from_exp (Value.to_exp input)))
                           in
                           List.exists
                             ~f:(fun (_,output) ->
                                 checker input (AngelicEval.to_value output))
                             outputs)
                       inputs)*)
                  (*not (C.accepts_term cand t)*)
              end)
          ~compare:C.size_compare(*fun (c1:C.t) (c2:C.t) ->
                                   let v1 = List.hd_exn (List.hd_exn c1.inputs) in
                                   let v2 = List.hd_exn (List.hd_exn c2.inputs) in
                                   Int.compare (Value.size v1) (Value.size v2)
                                 *)
          pqe.to_intersect
      in
      begin match min_unsat with
        | None -> None
        | Some (min,to_intersect) ->
          Consts.log (fun _ -> "Now intersecting: " ^ (Value.show (List.hd_exn (min.inputs))));
          let c = C.intersect min pqe.c in
          Consts.log (fun _ -> "Now minimizing: " ^ (Value.show (List.hd_exn (c.inputs))));
          let c = C.minimize c in
          (*Consts.log (fun _ -> string_of_float (Consts.max Consts.isect_times));*)
          let inputs = pqe.inputs in
          let v_to_c = pqe.v_to_c in
          Some
            (make_internal
               ~inputs
               ~c
               ~to_intersect
               ~v_to_c)
      end

    let make
        ~(inputs:ValueSet.t)
        ~(cs:C.t list)
        ~(v_to_c:ValToC.t)
      : t option =
      let (c,to_intersect) =
        extract_min_exn
          ~compare:C.size_compare
          cs
      in
      let rep_o = C.min_term_state c in
      begin match rep_o with
        | None ->
          None
        | Some rep ->
          Some
            {
              inputs       ;
              c            ;
              rep          ;
              v_to_c       ;
              to_intersect ;
              new_spec = None ;
            }
      end

    let update_with_new_spec
        ~(context:Context.t)
        ~(tin:Type.t)
        ~(tout:Type.t)
        ~(gs:GlobalState.t)
        ~(checker:Value.t -> Value.t -> bool)
        ~(pqe:t)
        ~(all_ins:Value.t list)
        ~(new_ins:Value.t list)
        ~(minimize:bool)
        ~(dupe:bool)
      : t option * GlobalState.t =
      let all_contained =
        List.for_all
          ~f:(fun vnew ->
              List.exists
                ~f:(fun vold ->
                    not (List.mem ~equal:Value.equal new_ins vold)
                    && (strict_functional_subvalue ~context ~ds:pqe.c.ds vnew vold)
                  )
                all_ins)
          new_ins
      in
      if !Consts.nonincremental || all_contained then
        let required_vs = ValueSet.insert_all pqe.inputs new_ins in
        let (cs,v_to_c,gs) =
          construct_full
            ~context
            ~tin
            ~tout
            ~checker
            ~gs
            all_ins
            required_vs
        in
        let qe =
          make
            ~inputs:required_vs
            ~cs
            ~v_to_c
        in
        (qe,gs)
      else
      let process_c (c:C.t) v (v_to_outs:Value.t -> Value.t list) : C.t =
        let c = C.copy c in
        let all_transitions = A.transitions c.a in
        let bad_transitions =
          List.filter
            ~f:(fun (t,ss,s) ->
                if FTAConstructor.Transition.equal_id (FTAConstructor.Transition.id t) FTAConstructor.Transition.Rec then
                  let so = FTAConstructor.State.destruct_vals s in
                  let sso =
                    distribute_option
                      (List.map ~f:FTAConstructor.State.destruct_vals ss)
                  in
                  begin match (sso,so) with
                    | (Some [(sins,_)],Some (souts,_)) ->
                      not
                        (List.for_all2_exn
                           ~f:(fun (v',vin) (v'',vout) ->
                               if Value.equal v v' then
                                 (assert (Value.equal v' v'');
                                  let finals = v_to_outs vin in
                                  (List.mem ~equal:Value.equal finals vout) &&
                                  true)
                               else
                                 true)
                           sins
                           souts)
                    | (None,None) -> false
                    | _ -> failwith "shouldn't happen"
                  end
                else
                  false)
            all_transitions
        in
        List.iter
          ~f:(fun (t,ss,s) ->
              C.remove_transition
                c
                t
                ss
                s)
          bad_transitions;
        let bad_finals =
          List.filter
            ~f:(fun s ->
                let (vs,_) = FTAConstructor.State.destruct_vals_exn s in
                let relevant =
                  List.find_map_exn
                    ~f:(fun (v1,v2) ->
                        if Value.equal v1 v then
                          Some v2
                        else
                          None)
                    vs
                in
                not (checker v relevant))
            (A.final_states c.a)
        in
        List.iter
          ~f:(fun fs ->
              C.remove_final_state c fs)
          bad_finals;
        let c =
          if minimize then
            (C.minimize c)
          else
            c
        in
        c
      in
      let (c,to_intersect,v_to_valids,v_to_c,gs) =
        List.fold
          ~f:(fun (c,to_intersect,v_map,v_to_c,gs) v ->
              let v_lookup v =
                List.Assoc.find_exn
                  ~equal:Value.equal
                  v_map
                  v
              in
              if List.mem ~equal:Value.equal c.inputs v then
                let c = process_c c v v_lookup in
                let v_map = (v,C.get_final_values c v)::v_map in
                (c,to_intersect,v_map,v_to_c,gs)
              else
                begin match split_by_first_satisfying
                              (fun (c:C.t) -> List.mem ~equal:Value.equal c.inputs v)
                              to_intersect with
                | None ->
                  let (c_des,gs) =
                    begin match ValToC.lookup v_to_c v with
                      | Some c_des ->
                        let c_des = ValToC.lookup_exn v_to_c v in
                        (process_c c_des v v_lookup,gs)
                      | None ->
                        construct_single_fta
                          ~context
                          ~tin
                          ~tout
                          ~gs
                          (fun v ->
                             begin match List.Assoc.find ~equal:Value.equal v_map v with
                               | None -> []
                               | Some vs -> vs
                             end)
                          v
                          checker
                    end
                  in
                  let v_map = (v,C.get_final_values c_des v)::v_map in
                  let v_to_c = ValToC.insert v_to_c v c_des in
                  let to_intersect =
                    if List.mem ~equal:Value.equal new_ins v then
                      (c_des::to_intersect)
                    else
                      to_intersect
                  in
                  (c,to_intersect,v_map,v_to_c,gs)
                | Some (cs1,c_des,cs2) ->
                  let c_des = process_c c_des v v_lookup in
                  let v_to_c = ValToC.insert v_to_c v c_des in
                  let v_map = (v,C.get_final_values c_des v)::v_map in
                  (c,cs1@c_des::cs2,v_map,v_to_c,gs)
                end)
          ~init:(pqe.c,pqe.to_intersect,[],pqe.v_to_c,gs)
          all_ins
      in
      let pqe =
        make_internal
          ~inputs:(ValueSet.insert_all pqe.inputs new_ins)
          ~c
          ~to_intersect
          ~v_to_c
      in
      (pqe,gs)

    let update_ds
        (pqe:t)
        (ds:C.TypeDS.t)
      : unit =
      C.update_ds ds pqe.c;
      List.iter ~f:(C.update_ds ds) pqe.to_intersect;
      List.iter ~f:(C.update_ds ds) (ValToC.value_list pqe.v_to_c);
      ()

    let update
        (pqe:t)
        ~(context:Context.t)
        ~(tin:Type.t)
        ~(tout:Type.t)
        ~(gs:GlobalState.t)
        (required_ins:Value.t list)
        (all_ins:Value.t list)
        (checker:Value.t -> Value.t -> bool)
        (ds:C.TypeDS.t)
      : t option * GlobalState.t =
      update_ds
        pqe
        ds;
      let new_ins =
        List.filter
          ~f:(fun v -> not (ValueSet.member pqe.inputs v))
          required_ins
      in
      update_with_new_spec
        ~gs
        ~context
        ~tin
        ~tout
        ~checker
        ~pqe
        ~all_ins
        ~new_ins
        ~minimize:true
        ~dupe:false

    let full_satisfies
        ~(context:Context.t)
        (pqe:t)
        (pred:Value.t -> Value.t -> bool)
        (orig_inputs:Value.t list)
      : bool =
      let term = A.TermState.to_term pqe.rep in
      let fune = C.term_to_safe_eval pqe.c.input_type pqe.c.output_type term (fun v1 v2 -> strict_functional_subvalue ~context ~ds:pqe.c.ds v2 v1) in
      List.for_all
        ~f:(fun vin ->
            let v = SafeEval.from_value vin in
            let e = SafeEval.value_to_exp v in
            let fulle = SafeEval.App (fune,e) in
            let vo = SafeEval.evaluate_with_holes ~eval_context:context.evals fulle in
            begin match vo with
              | None -> false
              | Some v ->
                let vout = SafeEval.to_value v in
                pred vin vout
            end)
        orig_inputs

    let priority
        (qe:t)
      : Float.t =
      (C.term_cost ~print:false (A.TermState.to_term qe.rep))

    let extract_recursive_calls
        (qe:t)
        (ts:A.TermState.t)
      : (A.TermState.t * FTAConstructor.State.t * int option) list =
      let t = A.TermState.to_term ts in
      List.concat_mapi
        ~f:(fun i c ->
            List.map
              ~f:(fun (s1,s2) -> (s1,s2,Some i))
              (C.extract_recursive_calls
                 (Option.value_exn
                    (A.accepting_term_state
                       c.a
                       t))))
        qe.to_intersect
      @(List.map ~f:(fun (r1,r2) -> (r1,r2,None)) (C.extract_recursive_calls ts))
  end

  type qe_res =
    | Intersected of PQE.t option
    | Failed of A.Term.t
    | Updated of PQE.t option
    | FoundResultProp of A.Term.t

  type synth_res =
    | IncreaseSize
    | FoundResult of A.Term.t

  type t =
    {
      context : Context.t ;
      tin : Type.t ;
      tout : Type.t ;
      gs : GlobalState.t ;
      pqe : PQE.t option ;
      last_processed : Value.t list ;
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

  let upgrade_from_failed_isect
      (a:t)
    : t =
    { a with
      gs = GlobalState.upgrade_from_failed_isect a.gs ;
      pqe = None ;
    }

  let synthesize
      ~(inputs:Value.t list)
      ~(ds:C.TypeDS.t)
      ~(pred:Value.t -> Value.t -> bool)
      ~(a:t)
    : (synth_res * t) =
    let orig_inputs = inputs in
    let orig_pred = pred in
    let context = a.context in
    if (List.length orig_inputs = 0) then
      (*Expr.of_type
         (Type.mk_arrow
            (Typecheck.concretify context.tc tin)
            (Typecheck.concretify context.tc tout))*)
      (FoundResult (C.term_of_type_exn ds a.tout),a)
    else
      let all_inputs =
        List.dedup_and_sort
          ~compare:Value.compare
          (List.concat_map
             ~f:(subvalues_full_of_same_type
                   ~context
                   ~ds)
             orig_inputs)
      in
      (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
        then v1 comes before v2 in terms of generating their FTAs. This is
        necessrary for ensuring that recursion is appropriately added *)
      let sorted_inputs =
        safe_sort
          ~compare:(fun v1 v2 ->
              if strict_functional_subvalue
                  ~context ~ds v1 v2 then
                Some (-1)
              else if strict_functional_subvalue ~context ~ds v2 v1 then
                Some 1
              else
                None)
          all_inputs
      in
      let process_queue_element
          (gs:GlobalState.t)
          (pqe:PQE.t)
        : qe_res * GlobalState.t =
        Consts.log (fun () -> "popped: " ^ Expr.show (C.term_to_exp_internals (A.TermState.to_term pqe.rep)));
        let subcalls =
          fun v ->
            C.get_final_values
              (ValToC.lookup_exn
                 pqe.v_to_c
                 v)
              v
        in
          begin match pqe.new_spec with
            | Some (ins,all_ins,pred,ds) ->
              let (ans,gs) = (PQE.update ~gs ~context ~tin:(tin a) ~tout:(tout a) pqe ins all_ins pred ds) in
              (Updated ans,gs)
            | None ->
              begin match PQE.intersect subcalls context ds pqe with
                | Some pqeo ->
                  (Intersected pqeo,gs)
                | None ->
                  Consts.log (fun _ -> "\n\nDone Intersecting! All Values" ^ ValueSet.show pqe.inputs);
                  let ts = pqe.rep in
                  if PQE.full_satisfies ~context pqe orig_pred orig_inputs then
                    begin
                      Consts.log (fun () -> "succeeded");
                      (FoundResultProp (A.TermState.to_term ts), gs)
                    end
                  else
                    begin
                      Consts.log (fun () -> "failed");
                      (Failed (A.TermState.to_term ts), gs)
                    end
              end
          end
      in
      let rec find_it_out
          (a:t)
        : synth_res * t =
        begin match a.pqe with
          | None ->
            Consts.log (fun () -> "new synth begun");
            let inputs = ValueSet.from_list orig_inputs in
            let (cs,v_to_c,gs) =
              construct_full
                ~context
                ~tin:a.tin
                ~tout:a.tout
                ~checker:pred
                ~gs:a.gs
                sorted_inputs
                inputs
            in
            let qe =
              PQE.make
                ~inputs
                ~cs
                ~v_to_c
            in
            begin match qe with
              | Some qe ->
                let pqe = Some qe in
                let a = { a with gs ; pqe ; } in
                (find_it_out a)
              | None ->
                (IncreaseSize,a)
            end
          | Some specs ->
            let (res,gs) = process_queue_element a.gs specs in
            begin match res with
              | FoundResultProp e -> (FoundResult e,a)
              | Updated qe ->
                begin match qe with
                  | Some pqe ->
                    Consts.log (fun () -> "succeeded update ");
                    Consts.log (fun () -> "new discovered value was: " ^ Expr.show (C.term_to_exp_internals (A.TermState.to_term pqe.rep)));
                    let a = { a with gs; pqe=Some(pqe); } in
                    find_it_out a
                  | None ->
                    (IncreaseSize,a)
                end
              | Intersected qe ->
                begin match qe with
                  | Some qe ->
                    Consts.log (fun () -> "succeeded intersect");
                    Consts.log (fun () -> "new discovered value was: " ^ Expr.show (C.term_to_exp_internals (A.TermState.to_term qe.rep)));
                    let a = { a with gs; pqe=Some(qe); } in
                    find_it_out a
                  | None ->
                    Consts.log (fun () -> "failed intersect");
                    (IncreaseSize,a)
                end
              | Failed term ->
                Consts.log (fun () -> "failed correctness");
                procd := TermSet.insert term !procd;
                add_all_subterms term;
                C.invalidate_computations specs.c;
                let madething =
                  PQE.make_internal
                    ~inputs:specs.inputs
                    ~c:specs.c
                    ~to_intersect:specs.to_intersect
                    ~v_to_c:specs.v_to_c
                in
                begin match madething with
                  | None ->
                    (IncreaseSize,a)
                  | Some pqe ->
                    let a = { a with pqe=(Some pqe) } in
                    find_it_out a
                end
            end
        end
      in
      (find_it_out a)

  let rec synthesize_caller
      (a:t)
      ~(ds:C.TypeDS.t)
      ~(pred:Value.t -> Value.t -> bool)
      ~(inputs:Value.t list)
    : t * Expr.t =
    Consts.log (fun _ -> "Synthesis started with size " ^ (string_of_int (GlobalState.get_num_applications a.gs)));
    let (synth_res,a) =
      synthesize
        ~pred
        ~inputs
        ~ds
        ~a
    in
    begin match synth_res with
      | IncreaseSize ->
        let a = upgrade_from_failed_isect a in
        synthesize_caller
          a
          ~ds
          ~pred
          ~inputs
      | FoundResult t ->
        (*let t = C.ensure_switches ds context t tout in*)
        (a,C.term_to_exp a.tin a.tout t)
    end

  let init
      ~(problem:Problem.t)
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
    : t =
    {
      context ;
      tin ;
      tout ;
      gs = GlobalState.empty ;
      pqe = None ;
      last_processed = [] ;
    }

  let synth
      (a:t)
      (inputs:Value.t list)
      (pred:Value.t -> Value.t -> bool)
    : t * Expr.t =
    let a =
      if !Consts.nonincremental then
        { a with
          gs = GlobalState.empty ;
          pqe = None ;
          last_processed = [] ;
        }
      else
        a
    in
    let context = (context a) in
    let tin = tin a in
    let tout = tout a in
    let all_values =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map ~f:Value.subvalues inputs) (*TODO*)
    in
    let ts =
      ([tin;tout]
       @(List.map ~f:Type.mk_named (Context.keys context.tc))
       @(Context.data context.ec)
       @(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) all_values))
    in
    let ds =
      C.create_ds_from_t_list_context
        ~context
        ts
    in
    let all_ins =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map
           ~f:(subvalues_full_of_same_type
                 ~context
                 ~ds)
           inputs)
    in
    (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
      then v1 comes before v2 in terms of generating their FTAs. This is
      necessrary for ensuring that recursion is appropriately added *)
    let sorted_ins =
      safe_sort
        ~compare:(fun v1 v2 ->
            if strict_functional_subvalue
                ~context ~ds v1 v2 then
              Some (-1)
            else if strict_functional_subvalue ~context ~ds v2 v1 then
              Some 1
            else
              None)
        all_ins
    in
    let a =
      begin match a.pqe with
        | None -> a
        | Some pq ->
          let pqe =
            Some
            { pq with
              new_spec = Some (inputs,sorted_ins,pred,ds)
            }
          in
          { a with pqe }
      end
    in
    Consts.log (fun () -> "inputs: " ^ (string_of_list Value.show inputs));
    synthesize_caller
      a
      ~inputs
      ~pred
      ~ds
end
