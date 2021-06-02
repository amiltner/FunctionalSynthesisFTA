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
    include DictOf(Value)(Value)

    let merge_single
        (c:t)
        (vin:Value.t)
        (vout:Value.t)
      : t option =
      begin match lookup c vin with
        | None ->
          Some
            (insert
               c
               vin
               vout)
        | Some vout' ->
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

    let update_checker
        ~(checker:Value.t -> Value.t -> bool)
        (c:t)
      : Value.t -> Value.t -> bool =
      let checker v1 v2 =
        begin match lookup c v1 with
          | None -> checker v1 v2
          | Some v ->
            Value.equal v2 v
        end
      in
      checker
  end
  module ValToC = DictOf(Value)(C)
  module ValueSet = SetOf(Value)
  module ValuePairSet = SetOf(PairOf(Value)(Value))
  module IndividualSettings = struct
    type t =
      {
        max_value_multiplier : Float.t ;
      }
    [@@deriving eq, hash, ord, show]

    let initial =
      {
        max_value_multiplier = 3.0 ;
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
        s : int ;
        kb : KnowledgeBase.t ;
      }
    [@@deriving eq, hash, ord, show]

    let empty : t =
      {
        d = D.empty ;
        s = 4;
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
      { gs with s = gs.s+1; kb = KnowledgeBase.empty }

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
        (v:Value.t)
      : int =
      gs.s

    let get_max_value_multiplier
        (s:t)
        (v:Value.t)
      : Float.t =
      let is = lookup s v in
      is.max_value_multiplier
  end

  module Added = struct
    module Elt = struct
      type t =
        {
          inputs       : ValueSet.t     ;
          constraints  : Constraints.t  ;
          nonpermitted : ValuePairSet.t ;
        }
      [@@deriving hash, show, equal, compare]
    end

    include SetOf(Elt)
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
      (num_applications:int)
    : C.t * GlobalState.t =
    let mvm = GlobalState.get_max_value_multiplier gs input in
    (*print_endline (string_of_int (Value.size_min_expr input));*)
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
                       (*print_endline (Value.show v1);
                         print_endline (string_of_list Value.show (sub_calls v1));*)
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
           let no_news =
             List.fold
               ~f:(fun last_adds i ->
                   begin match last_adds with
                     | None -> None
                     | Some (old_added,old_pruned) ->
                       let (d1,e1) = C.update_from_conversions c variant_unsafe_destruct_conversions in
                       let (d2,e2) = C.update_from_conversions c tuple_destructors in
                       let (d3,e3) = C.update_from_conversions c conversions in
                       let new_added = (List.length d1) + (List.length d2) + (List.length d3) in
                       let new_pruned = (List.length e1) + (List.length e2) + (List.length e3) in
                       (*print_endline (string_of_int (new_added));
                         print_endline (string_of_int (new_pruned));*)
                       if new_pruned > 0 &&
                          (new_added = 0 ||
                           (Float.to_int (Float.of_int new_added *. 5.0) < old_added && new_pruned > (Float.to_int (Float.of_int old_pruned *. 5.0)))) then
                         None
                       else
                         Some (new_added, new_pruned)
                   end)
               ~init:(Some (0,0))
               (range 0 (GlobalState.get_num_applications gs input))
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
          num_applications
      | Generated ans ->
        (ans,gs)
    end

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
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(checker:Value.t -> Value.t -> bool)
      ~(gs:GlobalState.t)
      (all_ins:Value.t list)
      (required_vs:ValueSet.t)
      (constraints:Constraints.t)
      (size:int)
    : (C.t list * ValToC.t * GlobalState.t) =
    (*print_endline "all ins";
      List.iter ~f:(print_endline % Value.show) all_ins;*)
    let checker v1 v2 =
      begin match Constraints.lookup constraints v1 with
        | None -> checker v1 v2
        | Some v ->
          Value.equal v2 v
      end
    in
    (*print_endline (string_of_list Value.show all_ins);*)
    (*print_endline @$ Expr.show (C.term_to_exp_internals desired_term);
      print_endline @$ string_of_int @$ Expr.size (C.term_to_exp_internals desired_term);*)
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
                size
            in
            (*print_endline @$ string_of_int (C.size res);*)
            (*print_endline "\n";
              print_endline (Value.show v);
              print_endline (string_of_bool (C.accepts_term res desired_term));*)
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

  module PQE = struct
    module Priority =
    struct
      type t = Float.t * Int.t * Int.t
      [@@deriving hash, show, equal]

      let compare (f1,i1,j1) (f2,i2,j2) =
        let fc = Float.compare f1 f2 in
        if fc = 0 then
          let ic = Int.compare i2 i1 in
          if ic = 0 then
            Int.compare j2 j1
          else
            ic
        else
          fc
    end

    type t =
      {
        inputs       : ValueSet.t     ;
        c            : C.t            ;
        to_intersect : C.t list       ;
        constraints  : Constraints.t  ;
        nonpermitted : ValuePairSet.t ;
        rep          : A.TermState.t  ;
        v_to_c       : ValToC.t       ;
      }
    [@@deriving eq, hash, ord, show, make]

    let make_internal
        ~(inputs:ValueSet.t)
        ~(c:C.t)
        ~(to_intersect:C.t list)
        ~(constraints:Constraints.t)
        ~(nonpermitted:ValuePairSet.t)
        ~(v_to_c:ValToC.t)
      : (t,KnowledgeBase.NPPFConj.t) either =
      let rep_o = C.min_term_state c in
      begin match rep_o with
        | None ->
          Right
            (ValuePairSet.as_list nonpermitted
            ,List.filter_map
                ~f:(fun v ->
                    begin match Constraints.lookup constraints v with
                      | None -> None
                      | Some v' -> Some (v,v')
                    end)
                c.inputs)
        | Some rep ->
          Left
            {
              inputs       ;
              c            ;
              constraints  ;
              nonpermitted ;
              rep          ;
              v_to_c       ;
              to_intersect ;
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
      : ((t,KnowledgeBase.NPPFConj.t) either) option =
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
                  (*print_endline (string_of_list Value.show cand.inputs);*)
                  let ans = not (C.accepts_term cand (A.TermState.to_term (Option.value_exn (C.min_term_state pqe.c)))) in
                  (*let accepter = A.accepting_term_state cand.a (A.TermState.to_term (Option.value_exn (C.min_term_state pqe.c))) in
                    print_endline (string_of_option A.TermState.show accepter);*)
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
        ~(nonpermitted:ValuePairSet.t)
        ~(v_to_c:ValToC.t)
      : t option =
      let (c,to_intersect) =
        extract_min_exn
          ~compare:C.size_compare
          cs
      in
      (*print_endline (Value.show (List.hd_exn (List.hd_exn c.inputs)));*)
      let rep_o = C.min_term_state c in
      (*print_endline (string_of_list Value.show c.inputs);*)
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

    let update_with_new_spec
        ~(checker:Value.t -> Value.t -> bool)
        ~(pqe:t)
        ~(all_ins:Value.t list)
        ~(new_ins:Value.t list)
        ~(constraints:Constraints.t)
        ~(nonpermitted:ValuePairSet.t)
        ~(minimize:bool)
      : (t,KnowledgeBase.NPPFConj.t) either =
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
                                  (not (ValuePairSet.member nonpermitted (vin,vout))))
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
              (*print_endline (FTAConstructor.Transition.show t);
                print_endline "ins";
                List.iter
                ~f:(print_endline % FTAConstructor.State.show)
                ss;
                print_endline "out";
                print_endline (FTAConstructor.State.show s);
                print_endline "\n\n";*)
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
      let (c,to_intersect,v_to_valids,v_to_c) =
        List.fold
          ~f:(fun (c,to_intersect,v_map,v_to_c) v ->
              let v_lookup v =
                List.Assoc.find_exn
                  ~equal:Value.equal
                  v_map
                  v
              in
              if List.mem ~equal:Value.equal c.inputs v then
                let c = process_c c v v_lookup in
                let v_map = (v,C.get_final_values c v)::v_map in
                (c,to_intersect,v_map,v_to_c)
              else
                begin match split_by_first_satisfying
                              (fun (c:C.t) -> List.mem ~equal:Value.equal c.inputs v)
                              to_intersect with
                | None ->
                  let c_des = ValToC.lookup_exn v_to_c v in
                  let c_des = process_c c_des v v_lookup in
                  let v_map = (v,C.get_final_values c_des v)::v_map in
                  let v_to_c = ValToC.insert v_to_c v c_des in
                  let to_intersect =
                    if List.mem ~equal:Value.equal new_ins v then
                      (c_des::to_intersect)
                    else
                      to_intersect
                  in
                  (c,to_intersect,v_map,v_to_c)
                | Some (cs1,c_des,cs2) ->
                  let c_des = process_c c_des v v_lookup in
                  let v_to_c = ValToC.insert v_to_c v c_des in
                  let v_map = (v,C.get_final_values c_des v)::v_map in
                  (c,cs1@c_des::cs2,v_map,v_to_c)
                end)
          ~init:(pqe.c,pqe.to_intersect,[],pqe.v_to_c)
          all_ins
      in
      let pqe =
        make_internal
          ~inputs:(ValueSet.insert_all pqe.inputs new_ins)
          ~c
          ~to_intersect
          ~constraints
          ~nonpermitted:nonpermitted
          ~v_to_c
      in
      pqe


    (*let update_nonpermitted
        (qe:t)
        ((v1,v2):Value.t * Value.t)
      : (t,KnowledgeBase.NPPFConj.t) either =
      (*print_endline (FTAConstructor.State.show (s1));
        print_endline (FTAConstructor.State.show s2);
        print_endline (string_of_option Int.to_string io);
        let tt = A.transitions_to qe.c.a s2 in
        print_endline "new transb";
        List.iter
        ~f:(fun (t,ss(*,out*)) ->
            print_endline @$ FTAConstructor.Transition.show t;
            List.iter
              ~f:(print_endline % FTAConstructor.State.show)
              ss;
            (*print_endline ("OUT: " ^ FTAConstructor.State.show out);*)
            print_endline "\n";)
        tt;
        print_endline "new transe";*)
      let (c,to_intersect,v_to_c) =
        begin match io with
          | None ->
            let c = C.copy qe.c in
            C.remove_transition
              c
              (C.rec_ c (snd (snd s2)))
              [s1]
              s2;
            (c,qe.to_intersect,qe.v_to_c)
          | Some i ->
            let (h,t) = extract_nth_exn i qe.to_intersect in
            let h = C.copy h in
            let v = List.hd_exn h.inputs in
            C.remove_transition
              h
              (C.rec_ h (snd (snd s2)))
              [s1]
              s2;
            let v_to_c = ValToC.insert qe.v_to_c v h in
            (qe.c,h::t,v_to_c)
        end
      in
      let availables = C.minimize c in
      (*print_endline @$ string_of_int (C.size availables);*)
      let c = availables in
      (*let tt = A.transitions_to c.a s2 in
        print_endline "new transb";
        List.iter
        ~f:(fun (t,ss(*,out*)) ->
            (*print_endline @$ FTAConstructor.Transition.show t;
            List.iter
              ~f:(print_endline % FTAConstructor.State.show)
              ss;*)
            (*print_endline ("OUT: " ^ FTAConstructor.State.show out);*)
            print_endline "\n";)
        tt;*)
      (*print_endline "new transe";
        print_endline "ANDDEN";
        print_endline "tried it";*)
      let nonpermitted =
        ValuePairSet.insert
          (s1,s2)
          qe.nonpermitted
      in
      let ans =
        make_internal
          ~inputs:qe.inputs
          ~c
          ~to_intersect:to_intersect
          ~constraints:qe.constraints
          ~nonpermitted
          ~v_to_c
      in
      ans*)

    let to_nppf_conj
        (qe:t)
      : KnowledgeBase.NPPFConj.t =
      (ValuePairSet.as_list qe.nonpermitted
      ,Constraints.as_kvp_list qe.constraints)

    let priority
        (qe:t)
      : Float.t * Int.t * Int.t =
      (C.term_cost ~print:false (A.TermState.to_term qe.rep)
      ,ValuePairSet.size qe.nonpermitted
      ,Constraints.size qe.constraints)

    let to_string_legible
        (qe:t)
      : string =
      let es = Expr.show (C.term_to_exp_internals (A.TermState.to_term qe.rep)) in
      let cs = Constraints.show qe.constraints in
      "term: " ^ es ^ "\nconstraints: " ^ cs ^ "\nnonpermitted: " ^ ValuePairSet.show qe.nonpermitted

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

    let to_added_key
        (qe:t)
      : Added.Elt.t =
      {
        inputs = qe.inputs ;
        constraints = qe.constraints ;
        nonpermitted = qe.nonpermitted ;
      }
  end

  module PQ = PriorityQueueOf(PQE)

  let safely_restricts_in_c
      (c:C.t)
      (inchoice:Value.t)
      (restriction:Value.t)
    : bool option =
    (*None means unsafe restriction, Some true means restricts outputs, false means no restricts outputs*)
    (*print_endline (Value.show inchoice);*)
    let vouts = C.get_final_values c inchoice in
    let vouts = List.dedup_and_sort ~compare:Value.compare vouts in
    (*print_endline (string_of_list Value.show vouts);
      print_endline "\n\n";*)
    if List.mem ~equal:Value.equal vouts restriction then
      Some (List.length vouts = 1)
    else
      (failwith "inv" ^ (Value.show inchoice) ^ "outv" ^ (Value.show restriction); None)

  let safely_restricts_outputs
      (pqe:PQE.t)
      (inset:ValueSet.t)
      (vtoc:ValToC.t)
      (inchoice:Value.t)
      (restriction:Value.t)
    : bool option =
    if ValueSet.member inset inchoice then
      begin
        if List.mem ~equal:(is_equal %% Value.compare) pqe.c.inputs inchoice then
          safely_restricts_in_c pqe.c inchoice restriction
        else
          safely_restricts_in_c (ValToC.lookup_exn vtoc inchoice) inchoice restriction
      end
    else
      begin
        safely_restricts_in_c
          (ValToC.lookup_exn vtoc inchoice)
          inchoice
          restriction
      end

  type qe_res =
    | NewQEs of PQE.t list
    | Intersected of (PQE.t,KnowledgeBase.NPPFConj.t) either
    | FoundResultProp of A.Term.t

  type synth_res =
    | IncreaseSize
    | FoundResult of A.Term.t

  let synthesize
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(gs:GlobalState.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(inputs:Value.t list)
      ~(pred:Value.t -> Value.t -> bool)
      ~(size:int)
    : (synth_res * GlobalState.t) =
    if (List.length inputs = 0) then
      (*Expr.of_type
         (Type.mk_arrow
            (Typecheck.concretify context.tc tin)
            (Typecheck.concretify context.tc tout))*)
      (FoundResult (C.term_of_type_exn ds tout),gs)
    else
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
        Consts.log (fun _ -> "\n\nPopped:");
        Consts.log (fun _ -> PQE.to_string_legible pqe);
        Consts.log (fun () -> "Priority: " ^ (PQE.Priority.show (PQE.priority pqe)));
        (*print_endline (string_of_bool @$ (C.accepts_term pqe.c desired_term));*)
        let subcalls =
          fun v ->
            C.get_final_values
              (ValToC.lookup_exn
                 pqe.v_to_c
                 v)
              v
        in
        if KnowledgeBase.falsifies (GlobalState.get_kb gs) (PQE.to_nppf_conj pqe) then
          begin
            Consts.log (fun _ -> "Falsified: by knowledge base");
            (NewQEs [],gs)
          end
        else
        begin match PQE.intersect subcalls context ds pqe with
          | Some pqeo ->
            (Intersected pqeo,gs)
          | None ->
            Consts.log (fun _ -> "\n\nDone Intersecting! All Values" ^ ValueSet.show pqe.inputs);
            let ts = pqe.rep in
            let rcs =
              List.dedup_and_sort
                ~compare:(triple_compare A.TermState.compare FTAConstructor.State.compare (compare_option Int.compare))
                ((PQE.extract_recursive_calls pqe ts)
                )
            in
            Consts.log (fun () -> "Recursive Calls:");
            Consts.log (fun () ->
                string_of_list
                  (string_of_triple
                     (FTAConstructor.State.show % A.TermState.get_state)
                     FTAConstructor.State.show
                     (string_of_option Int.to_string))
                  rcs);
            let rrs =
              List.concat_map
                ~f:(uncurry C.extract_recursive_requirements % (fun (v1,v2,_) -> (v1,v2)))
                rcs
            in
            let pure_rrs =
              List.dedup_and_sort
                ~compare:(pair_compare Value.compare Value.compare)
                (List.map
                   ~f:(fun (_,v1,v2,_) -> (v1,v2))
                   rrs)
            in
            print_endline (string_of_list (string_of_pair Value.show Value.show) pure_rrs);
            print_endline ("POSSIBLE CALLS");
            print_endline (string_of_list (string_of_pair Value.show (string_of_list Value.show)) (PQE.extract_possible_calls pqe inputs));
              if List.for_all
                  ~f:(fun (v1,v2) ->
                      List.mem
                        ~equal:(fun (v11,v12) (v21,v22) ->
                          Value.equal v11 v21 && Value.equal v12 v22)
                      pure_rrs
                      (v1,v2))
                (Constraints.as_kvp_list pqe.constraints) then
              let approvals =
                List.map
                  ~f:(fun (v1,v2) ->
                      Option.map
                        ~f:(fun ro -> (ro,(v1,v2)))
                        (safely_restricts_outputs pqe pqe.inputs pqe.v_to_c v1 v2))
                  pure_rrs
              in
              (*print_endline
                (string_of_list
                   (fun (v1,v2,v3,io,_) ->
                      (Value.show v1) ^ "," ^
                      (Value.show v2) ^ "," ^
                      (Value.show v3) ^ "," ^
                      (string_of_option Int.to_string io)
                   )
                   rrs);
                print_endline
                (string_of_list
                   (string_of_option
                      (string_of_pair
                         string_of_bool
                         (string_of_pair
                            Value.show
                            Value.show)))
                  approvals);*)
              let possible =
                distribute_option
                  approvals
              in
              begin match possible with
                | Some bs ->
                  print_endline
                    (string_of_list
                       (string_of_pair
                          Bool.to_string
                          (string_of_pair
                             Value.show
                             Value.show))
                    bs);
                  let new_constraints =
                    List.filter_map
                      ~f:(fun (b,nc) ->
                          if b && (ValueSet.member pqe.inputs (fst nc)) then
                            None
                          else
                            Some nc)
                      bs
                  in
                  if List.length new_constraints = 0 then
                    let e = (*C.term_to_exp tin tout*) (A.TermState.to_term ts) in
                    (*print_endline (string_of_int @$ Expr.size e);*)
                    (FoundResultProp e,gs)
                  else
                    let (gs,nonpermitteds) =
                      List.fold
                        ~f:(fun (gs,qes) r ->
                            let new_pqe =
                              PQE.update_with_new_spec
                                ~checker:pred
                                ~pqe
                                ~all_ins:sorted_inputs
                                ~new_ins:[]
                                ~constraints:pqe.constraints
                                ~nonpermitted:(ValuePairSet.insert r pqe.nonpermitted)
                                ~minimize:false
                            in
                            begin match new_pqe with
                              | Left qe -> (gs,qe::qes)
                              | Right nppf ->
                                (GlobalState.upgrade_kb gs nppf,qes)
                            end)
                        ~init:(gs,[])
                        pure_rrs
                    in
                    let merged_constraints_o =
                      Constraints.merge
                        pqe.constraints
                        new_constraints
                    in
                    (*print_endline
                      (string_of_list
                         (string_of_pair Value.show Value.show)
                         new_constraints);*)
                    (*print_endline "here2";*)
                    begin match merged_constraints_o with
                      | None ->
                        Consts.log
                          (fun _ -> "Falsified: popped value was found impossible with new constraints"
                                    ^ (string_of_list (string_of_pair Value.show Value.show) new_constraints));
                        let gs = GlobalState.upgrade_kb gs (KnowledgeBase.NPPFConj.add_partial_function_constraints (PQE.to_nppf_conj pqe) new_constraints) in
                        (NewQEs nonpermitteds
                        ,gs)
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
                        let new_ins =
                          List.map ~f:fst new_constraints
                        in
                        (*let inputs =
                          ValueSet.insert_all
                            pqe.inputs
                            (List.map ~f:fst new_constraints)
                          in*)
                        let qe =
                          PQE.update_with_new_spec
                            ~checker:(Constraints.update_checker ~checker:pred merged_constraints)
                            ~pqe
                            ~all_ins:sorted_inputs
                            ~new_ins
                            ~constraints:merged_constraints
                            ~nonpermitted:pqe.nonpermitted
                            ~minimize:true
                        in
                        (*let (cs,v_to_c,gs) =
                          construct_full
                            ~context
                            ~tin
                            ~tout
                            ~checker:pred
                            ~gs
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
                            ~nonpermitted:ValuePairSet.empty
                            ~v_to_c
                          in*)
                        begin match qe with
                          | Left qe ->
                            (NewQEs (qe::nonpermitteds),gs)
                          | Right nppf ->
                            Consts.log (fun _ -> "Falsified: popped value was found impossible2");
                            let gs = GlobalState.upgrade_kb gs nppf in
                            (NewQEs nonpermitteds,gs)
                        end
                    end
                | None ->
                  Consts.log (fun _ -> "Falsified: popped value was found impossible, and should not happen");
                  let (gs,nonpermitteds) =
                    List.fold
                      ~f:(fun (gs,qes) r ->
                          let new_pqe =
                            PQE.update_with_new_spec
                              ~checker:pred
                              ~pqe
                              ~all_ins:sorted_inputs
                              ~new_ins:[]
                              ~constraints:pqe.constraints
                              ~nonpermitted:(ValuePairSet.insert r pqe.nonpermitted)
                              ~minimize:false
                          in
                          begin match new_pqe with
                            | Left qe -> (gs,qe::qes)
                            | Right nppf ->
                              (GlobalState.upgrade_kb gs nppf,qes)
                          end)
                      ~init:(gs,[])
                      pure_rrs
                  in
                  (NewQEs nonpermitteds,gs)
              end
            else
              begin
                Consts.log (fun _ -> "Falsified: popped value did not use rrs");
                let gs = GlobalState.upgrade_kb gs (PQE.to_nppf_conj pqe) in
                let (gs,nonpermitteds) =
                  List.fold
                    ~f:(fun (gs,qes) r ->
                        let new_pqe =
                          PQE.update_with_new_spec
                            ~checker:pred
                            ~pqe
                            ~all_ins:sorted_inputs
                            ~new_ins:[]
                            ~constraints:pqe.constraints
                            ~nonpermitted:(ValuePairSet.insert r pqe.nonpermitted)
                            ~minimize:false
                        in
                        begin match new_pqe with
                          | Left qe -> (gs,qe::qes)
                          | Right nppf ->
                            (GlobalState.upgrade_kb gs nppf,qes)
                        end)
                    ~init:(gs,[])
                    pure_rrs
                in
                (NewQEs nonpermitteds,gs)
              end
        end
      in
      let rec find_it_out
          (gs:GlobalState.t)
          (a:Added.t)
          (specs:PQ.t)
        : synth_res * GlobalState.t =
        Consts.log (fun () -> "PQ Size: " ^ string_of_int (PQ.length specs));
        begin match PQ.pop specs with
          | Some (pqe,prio,specs) ->
            let (res,gs) = process_queue_element gs pqe in
            begin match res with
              | NewQEs new_qes ->
                let keys_qes =
                  List.map
                    ~f:(fun qe -> (PQE.to_added_key qe,qe))
                    new_qes
                in
                let keys_qes =
                  List.dedup_and_sort
                    ~compare:(fun (k1,_) (k2,_) -> Added.compare_elt k1 k2)
                    keys_qes
                in
                let keys_qes =
                  List.filter
                    ~f:(fun (k,_) -> not (Added.member a k))
                    keys_qes
                in
                let (keys,qes) = List.unzip keys_qes in
                Consts.log (fun () -> "New qes added is: " ^ string_of_int (List.length qes));
                Consts.log (fun () -> "New qes priorities: " ^ string_of_list PQE.Priority.show (List.map ~f:PQE.priority qes));
                let a = Added.insert_all a keys in
                find_it_out gs a (PQ.push_all specs qes)
              | FoundResultProp e -> (FoundResult e,gs)
              | Intersected qe ->
                begin match qe with
                  | Left qe ->
                    Consts.log (fun () -> "succeeded intersect with priority: " ^ (PQE.Priority.show (PQE.priority qe)));
                    Consts.log (fun () -> "new discovered value was: " ^ Expr.show (C.term_to_exp_internals (A.TermState.to_term qe.rep)));
                    find_it_out gs a (PQ.push specs qe)
                  | Right nppf ->
                    Consts.log (fun () -> "failed intersect");
                    let gs = GlobalState.upgrade_kb gs nppf in
                    find_it_out gs a specs
                end
            end
          | None -> (IncreaseSize,gs)
        end
      in
      let inputs = ValueSet.from_list inputs in
      let (cs,v_to_c,gs) =
        construct_full
          ~context
          ~tin
          ~tout
          ~checker:pred
          ~gs
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
          ~nonpermitted:ValuePairSet.empty
          ~v_to_c
      in
      (find_it_out gs Added.empty (PQ.from_list (Option.to_list qe)))

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
        List.hd_exn
          (AngelicEval.evaluate_with_holes
             ~eval_context
             (List.map ~f:(fun (v1,v2) -> (v1,[v2])) ios)
             (AngelicEval.App (cand_e,AngelicEval.value_to_exp input)))
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
                        List.hd_exn
                          (AngelicEval.evaluate_with_holes
                             ~eval_context
                             (List.map ~f:(fun (i,o) -> (i,[o])) angelic_ios)
                             to_expr)
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
                List.hd_exn
                  (AngelicEval.evaluate_with_holes
                     ~eval_context:(List.map ~f:(fun (i,e) -> (i,AngelicEval.from_exp e)) context.evals)
                     (List.map ~f:(fun (i,o) -> (i,[o])) ios)
                     (AngelicEval.App (cand_e,AngelicEval.value_to_exp inv)))
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
                List.hd_exn
                  (AngelicEval.evaluate_with_holes
                     ~eval_context:(List.map ~f:(fun (i,e) -> (i,AngelicEval.from_exp e)) context.evals)
                     (List.map ~f:(fun (i,o) -> (i,[o])) ios)
                     (AngelicEval.App (cand_e,AngelicEval.value_to_exp inv)))
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

  let rec synthesize_caller
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(pred:Value.t -> Value.t -> bool)
      ~(inputs:Value.t list)
      ~(size:int)
      ~(gs:GlobalState.t)
    : Expr.t =
    Consts.log (fun _ -> "Synthesis started with size " ^ (string_of_int (size+1)));
    let (synth_res,gs) =
      synthesize
        ~ds
        ~context
        ~tin
        ~tout
        ~pred
        ~inputs
        ~size:(size+1)
        ~gs
    in
    begin match synth_res with
      | IncreaseSize ->
        let gs = GlobalState.upgrade_from_failed_isect gs in
        synthesize_caller
          ~ds
          ~context
          ~tin
          ~tout
          ~pred
          ~inputs
          ~size:(size+1)
          ~gs
      | FoundResult t ->
        (*let t = C.ensure_switches ds context t tout in*)
        C.term_to_exp tin tout t
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
       ~size:3
       ~gs:GlobalState.empty)
end
