open MyStdLib
open Lang

module State =
struct
  type t = (Value.t * (Value.t option)) list * ClassifiedType.t
  [@@deriving eq, hash, ord, show]

  let print a b = pp b a

  let product a b =
    begin match (a,b) with
      | ((avs,at), (bvs,bt)) ->
        if ClassifiedType.equal at bt then
          Some (((avs@bvs),at))
        else
          None
    end
end

module Transition =
struct
  type id =
    | FunctionApp of Id.t
    | Apply
    | VariantConstruct of Id.t
    | UnsafeVariantDestruct of Id.t
    | TupleConstruct of int
    | TupleDestruct of int * int
    | Var
    | LetIn
    | Rec
    | VariantSwitch of Id.t list
  [@@deriving eq, hash, ord, show]
  type t_node = (id * Type.t * int)
  [@@deriving eq, hash, ord, show]
  type t = t_node hash_consed
  [@@deriving eq, hash, ord, show]

  let to_expr
      (t:t)
      (es:AngelicEval.expr list)
    : AngelicEval.expr =
    begin match fst3 t.node with
      | FunctionApp i -> AngelicEval.Var i
      | Apply ->
        begin match es with
          | [e1;e2] -> AngelicEval.App (e1,e2)
          | _ -> failwith "bad1"
        end
      | VariantConstruct i ->
        begin match es with
          | [e] -> AngelicEval.Ctor (i,e)
          | _ -> failwith ("bad2:" ^ (string_of_list AngelicEval.show_expr es))
        end
      | UnsafeVariantDestruct i ->
        begin match es with
          | [e] -> AngelicEval.Unctor (i,e)
          | _ -> failwith "bad3"
        end
      | TupleConstruct _ ->
        AngelicEval.Tuple es
      | TupleDestruct (_,i) ->
        begin match es with
          | [e] -> AngelicEval.Proj (i,e)
          | _ -> failwith "bad4"
        end
      | Var -> AngelicEval.Var (Id.create "x")
      | LetIn -> failwith "bad5"
      | Rec ->
        begin match es with
          | [e] ->
            AngelicEval.AngelicF e
          | _ ->
            failwith "bad6"
        end
      | VariantSwitch ids ->
        begin match es with
          | e::es ->
            let branches =
              List.map2_exn
                ~f:(fun i e -> (i,e))
                ids
                es
            in
            AngelicEval.Match (e,Id.create "_",branches)
          | _ -> failwith "bad7"
        end
    end

  let table = HashConsTable.create 1000

  let create
      (node:t_node)
    : t =
    HashConsTable.hashcons
      hash_t_node
      compare_t_node
      table
      node

  let node
      (v:t)
    : t_node =
    v.node

  let id
      (v:t)
    : id =
    fst3 (node v)

  let get_type
      (v:t)
    : Type.t =
    snd3 (node v)

  let print_id id =
    match id with
    | FunctionApp x -> Id.show x
    | VariantConstruct x -> "Variant(" ^ MyStdLib.Id.to_string x ^ ")"
    | TupleConstruct i -> "Tuple(" ^ (string_of_int i) ^ ")"
    | Var -> "Var"
    | LetIn -> "LetIn"
    | Rec -> "Rec"
    | UnsafeVariantDestruct t -> "VariantUnsafe(" ^ (Id.show t) ^ ")"
    | TupleDestruct (t,i) ->
      "TupleProj("
      ^ (string_of_int t)
      ^ ","
      ^ (string_of_int i)
      ^ ")"
    | VariantSwitch (bs) ->
      "SwitchOn(" ^ (String.concat ~sep:"," (List.map ~f:Id.to_string bs)) ^ ")"
    | Apply ->
      "Apply"
  

  (*let rec_ = create (Rec,1)*)

  let arity = trd3 % node
end

module Make(A : Automata.Automaton with module Symbol := Transition and module State := State) = struct
  module TypeDS = struct
    include
      DisjointSetWithSetDataOf
        (struct
          include Type
          let preferred t1 t2 =
            begin match (Type.node t1,Type.node t2) with
              | (Variant _,Variant _)
              | (Arrow _,Arrow _)
              | (Tuple _,Tuple _) ->
                Type.size t1 < Type.size t2
              | _ ->
                begin match Type.node t1 with
                  | Variant _
                  | Arrow _
                  | Tuple _ -> true
                  | _ -> false
                end
            end
        end)
        (BoolModule)
        (struct
          type t = Type.t -> bool
          let v = (Option.is_some % Type.destruct_mu)
        end)
        (struct
          type t = bool -> bool -> bool
          let v = (||)
        end)

    let is_recursive_type
        (x:t)
        (t:Type.t)
      : bool =
      snd
        (find_representative
           x
           t)
  end

  module StateSet = SetOf(State)
  module InputsAndTypeToStates = DictOf(ClassifiedType)(StateSet)
  module TransitionSet = SetOf(Transition)

  type t =
    {
      a                  : A.t                        ;
      mutable d          : InputsAndTypeToStates.t    ;
      ds                 : TypeDS.t                   ;
      inputs             : Value.t list               ;
      mutable tset       : TransitionSet.t            ;
      final_candidates   : Value.t -> Value.t -> bool ;
      all_types          : Type.t list                ;
      mutable up_to_date : bool                       ;
      input_type         : Type.t                     ;
      output_type        : Type.t                     ;
      abstraction        : AbstractionDict.t             ;
      mutable all_states : StateSet.t                 ;
      mutable min_term_state : A.TermState.t option option ;
    }
  [@@deriving show]

  let copy (c:t)
    : t =
    { c with
      a = A.copy c.a ;
    }

  let equal _ _ = failwith "not implemented"
  let hash_fold_t _ _ = failwith "not implemented"
  let hash _ = failwith "not implemented"
  let compare _ _ = failwith "not implemented"

  let fid = Id.create "f"
  let xid = Id.create "x"

  let rec term_to_exp_internals
      (Term (t,ts):A.term)
    : Expr.t =
    begin match Transition.id t with
      | Apply ->
        begin match ts with
          | [t1;t2] ->
            let e1 = term_to_exp_internals t1 in
            let e2 = term_to_exp_internals t2 in
            Expr.mk_app e1 e2
          | _ -> failwith "not permitted"
        end
      | FunctionApp e ->
        List.fold
          ~f:(fun acc bt ->
              Expr.mk_app
                acc
                (term_to_exp_internals bt))
          ~init:(Expr.mk_var e)
          ts
      | VariantConstruct c ->
        begin match ts with
          | [t] ->
            Expr.mk_ctor c (term_to_exp_internals t)
          | _ -> failwith "incorrect setup"
        end
      | UnsafeVariantDestruct c ->
        begin match ts with
          | [t] ->
            Expr.mk_unctor
              c
              (term_to_exp_internals t)
          | _ -> failwith "incorrect setup"
        end
      | TupleConstruct _ ->
        Expr.mk_tuple
          (List.map
             ~f:term_to_exp_internals
             ts)
      | Var ->
        Expr.mk_var xid
      | Rec ->
        begin match ts with
          | [t] ->
            Expr.mk_app (Expr.mk_var fid) (term_to_exp_internals t)
          | _ -> failwith "incorrect"
        end
      | VariantSwitch is ->
        begin match ts with
          | t::ts ->
            (* TODO, make destructors *)
            let e = term_to_exp_internals t in
            let its = List.zip_exn is ts in
            let ies = List.map ~f:(fun (i,t) -> (i,term_to_exp_internals t)) its in
            Expr.mk_match e (Id.wildcard) ies
          | [] -> failwith "cannot happen"
        end
      | TupleDestruct (_,i) ->
        Expr.mk_proj i (term_to_exp_internals (List.hd_exn ts))
      | _ -> failwith "not permitted"
    end

  let term_to_exp
      (tin:Type.t)
      (tout:Type.t)
      (t:A.Term.t)
    : Expr.t =
    let internal = term_to_exp_internals t in
    Expr.mk_fix
      fid
      (Type.mk_arrow tin tout)
      (Expr.mk_func (xid,tin) internal)

  let term_to_angelic_exp
      (tin:Type.t)
      (t:A.term)
    : AngelicEval.expr =
    let rec term_to_angelic_exp
        (Term (t,ts):A.term)
      : AngelicEval.expr =
      AngelicEval.(begin match Transition.id t with
          | Apply ->
            begin match ts with
              | [t1;t2] ->
                let e1 = term_to_angelic_exp t1 in
                let e2 = term_to_angelic_exp t2 in
                App (e1,e2)
              | _ -> failwith "not permitted"
            end
          | FunctionApp e ->
            List.fold
              ~f:(fun acc bt ->
                  App
                    (acc
                    ,(term_to_angelic_exp bt)))
              ~init:(AngelicEval.Var e)
              ts
          | VariantConstruct c ->
            begin match ts with
              | [t] ->
                Ctor (c,term_to_angelic_exp t)
              | _ -> failwith "incorrect setup"
            end
          | UnsafeVariantDestruct c ->
            begin match ts with
              | [t] ->
                Unctor
                  (c
                  ,term_to_angelic_exp t)
              | _ -> failwith "incorrect setup"
            end
          | TupleConstruct _ ->
            Tuple
              (List.map
                 ~f:term_to_angelic_exp
                 ts)
          | Var ->
            Var xid
          | Rec ->
            begin match ts with
              | [t] ->
                AngelicF (term_to_angelic_exp t)
              | _ -> failwith "incorrect"
            end
          | VariantSwitch is ->
            begin match ts with
              | t::ts ->
                (* TODO, make destructors *)
                let e = term_to_angelic_exp t in
                let its = List.zip_exn is ts in
                let ies = List.map ~f:(fun (i,t) -> (i,term_to_angelic_exp t)) its in
                Match (e,(Id.wildcard),ies)
              | [] -> failwith "cannot happen"
            end
          | TupleDestruct (_,i) ->
            Proj (i,(term_to_angelic_exp (List.hd_exn ts)))
          | _ -> failwith "not permitted"
        end)
    in
    Func
      ((xid,tin)
      ,term_to_angelic_exp t)

  let rec term_of_type ds t =
    let (desired_t,_) = TypeDS.find_representative ds t in
    begin match Type.node desired_t with
      | Named i -> failwith "ah"
      | Arrow (t1,t2) -> failwith "ah"
      | Tuple ts ->
        let eso = List.map ~f:(term_of_type ds) ts in
        begin match distribute_option eso with
          | None -> None
          | Some es ->
            Some
              (A.Term
                 (Transition.create
                    (Transition.TupleConstruct (List.length es)
                    ,desired_t
                    ,List.length es)
                 ,es))
        end
      | Mu (_,t) ->
        term_of_type ds t
      | Variant branches ->
        List.fold
          ~f:(fun acco (i,t) ->
              begin match acco with
                | None ->
                  let eo = term_of_type ds t in
                  Option.map
                    ~f:(fun e ->
                        A.Term
                          (Transition.create
                             (Transition.VariantConstruct i
                             ,desired_t
                             ,1)
                          ,[e]))
                    eo
                | Some e -> Some e
              end)
          ~init:None
          branches
    end

  let term_of_type_exn
      (ds:TypeDS.t)
      (x:Type.t)
    : A.Term.t =
    Option.value_exn (term_of_type ds x)


  let rec extract_unbranched_switches
      (Term (t,ts):A.term)
    : (A.term * Id.t) list =
    begin match Transition.id t with
       | Apply ->
         begin match ts with
           | [t1;t2] ->
             let l1 = extract_unbranched_switches t1 in
             let l2 = extract_unbranched_switches t2 in
             l1@l2
           | _ -> failwith "not permitted"
         end
       | FunctionApp _ ->
         List.concat_map ~f:extract_unbranched_switches ts
       | VariantConstruct c ->
         begin match ts with
           | [t] ->
             extract_unbranched_switches t
           | _ -> failwith "incorrect setup"
         end
       | UnsafeVariantDestruct i ->
         begin match ts with
           | [t] ->
             let l = extract_unbranched_switches t in
             (t,i)::l
           | _ -> failwith "incorrect setup"
         end
       | TupleConstruct _ ->
         List.concat_map ~f:extract_unbranched_switches ts
       | Var ->
         []
       | Rec ->
         begin match ts with
           | [t] ->
             extract_unbranched_switches t
           | _ -> failwith "incorrect"
         end
       | VariantSwitch is ->
         begin match ts with
           | t::ts ->
             let matched_t = t in
             let l = extract_unbranched_switches t in
             l@
             (List.concat_map
                ~f:(fun t ->
                    let l = extract_unbranched_switches t in
                    List.filter ~f:(fun (t,_) -> not (A.Term.equal t matched_t)) l)
                ts)
           | [] -> failwith "cannot happen"
         end
       | TupleDestruct _ ->
         begin match ts with
           | [t] ->
             extract_unbranched_switches t
           | _ -> failwith "not permitted"
         end
       | LetIn -> failwith "not permitted"
      end

  let rec ensure_switches
      (ds:TypeDS.t)
      (context:Context.t)
      (e:A.Term.t)
      (desired_type:Type.t)
    : A.Term.t =
    let unbranched = extract_unbranched_switches e in
    let all_ts_by_exp =
      group_by
        ~key:(fst)
        ~equal:A.Term.equal
        unbranched
    in
    if List.is_empty all_ts_by_exp then
      e
    else
      let e =
        List.fold
          ~f:(fun t tbis ->
              let t_orig = t in
              begin match tbis with
                | (tb,i)::_ ->
                  let i_orig = i in
                  let vc = context.vc in
                  let its = Context.find_exn vc i in
                  let (t,_) = TypeDS.find_representative ds (Type.mk_variant its) in
                  let its = Type.destruct_variant_exn t in
                  let ts =
                    List.map
                      ~f:(fun (i,_) ->
                          if Id.equal i i_orig then
                            t_orig
                          else
                            term_of_type_exn ds desired_type)
                      its
                  in
                  let is = List.map ~f:fst its in
                  A.Term
                    (Transition.create
                       (Transition.VariantSwitch is
                       ,t
                       ,1+(List.length is))
                    ,tb::ts)
                | _ -> failwith "bad"
              end)
          ~init:e
          all_ts_by_exp
      in
      ensure_switches
        ds
        context
        e
        desired_type

  module EasyTerm = struct
    type t_node =
      | App of string * t list
      | VC of string * t
      | UVD of string * t
      | TC of t list
      | TD of int * int * t
      | Var
      | Rec of t
      | VSwitch of string list * t list
    and t = (Type.t * t_node)

    let rec to_term
        ((ty,e):t)
      : A.Term.t =
      let mk_term
          (id:Transition.id)
          (children:A.Term.t list)
        : A.Term.t =
        let s = List.length children in
        A.Term (Transition.create (id,ty,s),children)
      in
      begin match e with
        | Var ->
          mk_term Transition.Var []
        | App (i,ets) ->
          let ts = List.map ~f:to_term ets in
          mk_term (Transition.FunctionApp (Id.create i)) ts
        | VC (i,et) ->
          mk_term (Transition.VariantConstruct (Id.create i)) [to_term et]
        | UVD (i,et) ->
          mk_term (Transition.UnsafeVariantDestruct (Id.create i)) [to_term et]
        | TC (ets) ->
          let ts = List.map ~f:to_term ets in
          mk_term (Transition.TupleConstruct (List.length ets)) ts
        | TD (i1,i2,et) ->
          mk_term (Transition.TupleDestruct (i1,i2)) [to_term et]
        | Rec et ->
          mk_term (Transition.Rec) [to_term et]
        | VSwitch (ids,ets) ->
          let ts = List.map ~f:to_term ets in
          mk_term (Transition.VariantSwitch (List.map ~f:Id.create ids)) ts
      end
    end

  let get_type_rep
      (c:t)
      (t:Type.t)
    : Type.t =
    fst
      (TypeDS.find_representative
         c.ds
         t)

  let is_recursive_type
      (c:t)
      (t:Type.t)
    : bool =
    snd
      (TypeDS.find_representative
         c.ds
         t)

  let invalidate_computations
      (c:t)
    : unit =
    c.min_term_state <- None

  let get_final_values
      (c:t)
      (vin:Value.t)
    : Predicate.t list =
    let final_states = A.final_states c.a in
    List.concat_map
      ~f:(fun s ->
          begin match s with
            | ((vinsvouts),_) ->
              List.filter_map
                ~f:(fun (vin',vout) ->
                    begin match vout with
                      | None -> failwith "bad finals"
                      | Some vout ->
                        if Value.equal vin vin' then
                          Some vout
                        else
                          None
                    end)
                vinsvouts
          end)
      final_states

  let get_states
      (c:t)
      ((t,cl):ClassifiedType.t)
    : State.t list =
    begin match InputsAndTypeToStates.lookup c.d (get_type_rep c t,cl) with
      | None -> []
      | Some ss -> StateSet.as_list ss
    end

  let val_state
      (c:t)
      (vinsvouts:(Value.t * Value.t option) list)
      ((t,cl):ClassifiedType.t)
    : State.t =
    let t = get_type_rep c t in
    let vinsvouts =
      List.map
        ~f:(fun (vin,vout) ->
            begin match vout with
              | None -> (vin, None)
              | Some vout ->
                if !Consts.use_abstraction then
                  (vin,Some (AbstractionDict.abstract c.abstraction vin vout t))
                else
                  (vin,Some vout)
            end)
        vinsvouts
    in
    (vinsvouts,(t,cl))

  let add_state
      (c:t)
      (vinsvouts:(Value.t * (Value.t option)) list)
      ((t,cl):ClassifiedType.t)
    : unit =
    let t = get_type_rep c t in
    let s = val_state c vinsvouts (t,cl) in
    let to_add =
      begin match InputsAndTypeToStates.lookup c.d (t,cl) with
        | None ->
          StateSet.singleton s
        | Some ss ->
          StateSet.insert s ss
      end
    in
    let all_states = StateSet.insert s c.all_states in
    let d =
      InputsAndTypeToStates.insert
        c.d
        (t,cl)
        to_add
    in
    begin
      if Type.equal t c.output_type
         && TermClassification.equal cl TermClassification.Introduction
         && List.for_all
              ~f:(fun (vin,vouto) ->
                  begin match vouto with
                    | None -> false
                    | Some vout -> c.final_candidates vin vout
                  end)
              vinsvouts
      then
        A.add_final_state c.a s
      else
        ()
    end;
    c.d <- d;
    c.all_states <- all_states;
    invalidate_computations c

  let update_tset
      (c:t)
      (trans:Transition.t)
    : unit =
    c.tset <- TransitionSet.insert trans c.tset

  let add_transition
      (c:t)
      (trans_id:Transition.id)
      (sins:State.t list)
      (sout:State.t)
      (tout:Type.t)
      (ensure_state:bool)
    : unit =
    let tout = get_type_rep c tout in
    update_tset
      c
      (Transition.create (trans_id,tout,List.length sins));
    if ensure_state then
      begin
        let (vinsvouts,t) = sout in
        add_state c vinsvouts t;
        A.add_transition
          c.a
          (Transition.create (trans_id,tout,List.length sins))
          sins
          sout;
        invalidate_computations c
      end
    else if StateSet.member c.all_states sout then
      begin
        A.add_transition
          c.a
          (Transition.create (trans_id,tout,List.length sins))
          sins
          sout;
        invalidate_computations c;
      end
    else
      ()

  let remove_transition
      (c:t)
      (trans:Transition.t)
      (sins:State.t list)
      (sout:State.t)
    : unit =
    A.remove_transition c.a trans sins sout;
    invalidate_computations c

  let evaluate
      (c:t)
      (input:Predicate.t list)
      (f:Value.t list -> Value.t list)
      (args:State.t list)
      ((t,cl):ClassifiedType.t)
    : State.t list =
    let vs = List.map ~f:(List.map ~f:snd % fst) args in
    let args =
      begin match vs with
        | [] -> List.init ~f:(func_of []) (List.length input)
        | _ -> List.transpose_exn vs
      end
    in
    let outs =
      List.map
        ~f:(fun vins ->
            begin match distribute_option vins with
              | None -> [None]
              | Some vs ->
                begin match f vs with
                  | [] -> [None]
                  | x -> List.map ~f:Option.some x
                end
            end)
        args
    in
    let outsl = List.transpose_exn outs in
    List.map
      ~f:(fun outs ->
          let in_outs = List.zip_exn input outs in
          val_state c in_outs (t,cl))
      outsl
    (*let args =
      List.map
        ~f:(List.map
              ~f:Value.to_exp)
        args
      in
    let full_exps =
      List.map
        ~f:(List.fold
              ~f:Expr.mk_app
              ~init:e)
        args
    in
      let outs = List.map ~f:Eval.evaluate full_exps in*)

  let evaluate
      (c:t)
      (input:Predicate.t list)
      (f:Value.t list -> Value.t list)
      (args:State.t list)
      ((t,cl):ClassifiedType.t)
    : State.t list =
    let vs = List.map ~f:(List.map ~f:snd % fst) args in
    let args =
      begin match vs with
        | [] -> List.init ~f:(func_of []) (List.length input)
        | _ -> List.transpose_exn vs
      end
    in
    let outs =
      List.map
        ~f:(fun vins ->
            begin match distribute_option vins with
              | None -> [None]
              | Some vs ->
                begin match f vs with
                  | [] -> [None]
                  | x -> List.map ~f:Option.some x
                end
            end)
        args
    in
    let outsl = List.transpose_exn outs in
    List.map
      ~f:(fun outs ->
          let in_outs = List.zip_exn input outs in
          val_state c in_outs (t,cl))
      outsl
    (*let args =
      List.map
        ~f:(List.map
              ~f:Value.to_exp)
        args
      in
    let full_exps =
      List.map
        ~f:(List.fold
              ~f:Expr.mk_app
              ~init:e)
        args
    in
      let outs = List.map ~f:Eval.evaluate full_exps in*)

  let evaluate_full
      (c:t)
      (input:Predicate.t list)
      (f:Value.t -> (Value.t option) list -> (Value.t option) list)
      (args:State.t list)
      ((t,cl):ClassifiedType.t)
    : State.t list =
    let vs = List.map ~f:(List.map ~f:snd % fst) args in
    let args =
      begin match vs with
        | [] -> List.map ~f:(fun input -> (input,[])) input
        | _ ->
          List.zip_exn
            input
            (List.transpose_exn vs)
      end
    in
    let outs =
      List.map
        ~f:(fun (input,vins) ->
            List.dedup_and_sort
              ~compare:(option_compare Value.compare)
              (f input vins))
        args
    in
    let outsl = combinations outs in
    List.map
      ~f:(fun outs ->
          let in_outs = List.zip_exn input outs in
          val_state c in_outs (t,cl))
      outsl

  let update_from_conversions
      ?(ensure_state:bool = true)
      (c:t)
      (conversions:
         ((Transition.id
           * (Value.t -> (Value.t option) list -> (Value.t option) list)
           * (ClassifiedType.t list) * ClassifiedType.t) list))
    : unit =
    let ids_ins_outs =
      List.concat_map
        ~f:(fun (i,e,tins,tout) ->
            let inputs = c.inputs in
            let args_choices =
              List.map
                ~f:(fun t -> get_states c t)
                tins
            in
            let args_list =
              combinations
                args_choices
            in
            List.concat_map
              ~f:(fun ins ->
                  let outs = evaluate_full c inputs e ins tout in
                  List.map
                    ~f:(fun out -> (i,ins,out,fst tout))
                    outs)
              args_list)
        conversions
    in
    List.iter
      ~f:(fun (i,ins,out,tout) ->
          add_transition
            c
            i
            ins
            out
            tout
            ensure_state)
      ids_ins_outs

  let update_from_simple_conversions
      ?(ensure_state:bool = true)
      (c:t)
      (conversions:
         ((Transition.id
           * (Value.t -> Value.t list -> Value.t list)
           * (ClassifiedType.t list) * ClassifiedType.t) list))
    : unit =
    let update_value_conversion f =
      fun input vins ->
        begin match distribute_option vins with
          | None -> [None]
          | Some vs ->
            begin match f input vs with
              | [] -> [None]
              | x -> List.map ~f:Option.some x
            end
        end
    in
    let conversions =
      List.map
        ~f:(fun (tid,f,cts,ct) ->
            (tid,update_value_conversion f,cts,ct))
        conversions
    in
    update_from_conversions ~ensure_state c conversions

  let create_ds_from_t_list_context
      ~(context:Context.t)
      (ts:Type.t list)
    : TypeDS.t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes context.tc)
           ts)

    in
    TypeDS.create_from_list
      ~equiv:(Typecheck.type_equiv context.tc)
      all_types

  let create_ds_from_t_list
      ~(problem:Problem.t)
      (ts:Type.t list)
    : TypeDS.t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes problem.tc)
           ts)

    in
    TypeDS.create_from_list
      ~equiv:(Typecheck.type_equiv problem.tc)
      all_types

  let initialize_context
      ~(context:Context.t)
      ~(abstraction:AbstractionDict.t)
      (ts:Type.t list)
      (inputs:Value.t list)
      ((input_type,output_type):Type.t * Type.t)
      (final_candidates:Value.t -> Value.t -> bool)
    : t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes context.tc)
           ts)

    in
    let ds = create_ds_from_t_list_context ~context ts in
    let a = A.empty () in
    let d = InputsAndTypeToStates.empty in
    let input_vals = inputs in
    let tset = TransitionSet.empty in
    let (input_type,_) = TypeDS.find_representative ds input_type in
    let (output_type,_) = TypeDS.find_representative ds output_type in
    let all_states = StateSet.empty in
    let c =
      {
        a                 ;
        d                 ;
        ds                ;
        inputs            ;
        tset              ;
        final_candidates  ;
        all_types         ;
        up_to_date = true ;
        input_type        ;
        output_type       ;
        min_term_state = None;
        all_states        ;
        abstraction       ;
      }
    in
    add_transition
      c
      Var
      []
      (val_state c (List.map ~f:(fun i -> (i,Some i)) input_vals) (input_type,TermClassification.Elimination))
      input_type
      true;
    add_transition
      c
      Var
      []
      (val_state c (List.map ~f:(fun i -> (i,Some i)) input_vals) (input_type,TermClassification.Elimination))
      input_type
      true;
    c

  let initialize
      ~(problem:Problem.t)
      ~(abstraction:AbstractionDict.t)
      (ts:Type.t list)
      (inputs:Value.t list)
      ((input_type,output_type):Type.t * Type.t)
      (final_candidates:Value.t -> Value.t -> bool)
    : t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes problem.tc)
           ts)

    in
    let ds = create_ds_from_t_list ~problem ts in
    let a = A.empty () in
    let d = InputsAndTypeToStates.empty in
    let input_vals = inputs in
    let tset = TransitionSet.empty in
    let (input_type,_) = TypeDS.find_representative ds input_type in
    let (output_type,_) = TypeDS.find_representative ds output_type in
    let all_states = StateSet.empty in
    let c =
      {
        a                 ;
        d                 ;
        ds                ;
        inputs            ;
        tset              ;
        final_candidates  ;
        all_types         ;
        up_to_date = true ;
        input_type        ;
        output_type       ;
        min_term_state = None;
        all_states        ;
        abstraction       ;
      }
    in
    add_transition
      c
      Var
      []
      (val_state c (List.map ~f:(fun i -> (i,Some i)) input_vals) (input_type,TermClassification.Elimination))
      input_type
      true;
    add_transition
      c
      Var
      []
      (val_state c (List.map ~f:(fun i -> (i,Some i)) input_vals) (input_type,TermClassification.Elimination))
      input_type
      true;
    c

  let get_all_types
      (c:t)
    : Type.t list =
    c.all_types

  let get_all_state_pairs
      (c:t)
    : (Value.t list) list =
    let all_states = A.states c.a in
    let all_pairs =
      List.map
        ~f:(fun (vsps,_) ->
            List.filter_map
              ~f:(fun (vin,vouto) ->
                  Option.map ~f:(fun vout -> vin) vouto)
              vsps)
        all_states
    in
    List.dedup_and_sort
      ~compare:(compare_list ~cmp:Value.compare)
      all_pairs

  (*let add_let_ins
      (c:t)
    : unit =
    List.iter
      ~f:(fun (s1,s2) ->
          begin match (s1,s2) with
            | (Vals ([v11,v12],_), Vals ([v21,v22],t)) ->
              if c.final_candidates v21 v22 &&
                 (Value.equal v12 v21) &&
                 List.mem ~equal:Value.equal (Value.strict_subvalues v11) v12
              then
                add_transition
                  c
                  LetIn
                  [s1;s2]
                  (val_state c [v11,v22] t)
                  true
              else
                ()
            | _ -> ()
          end)
      (List.cartesian_product (A.states c.a) (A.states c.a))*)

  let add_final_state
      (c:t)
      (s:State.t)
    : unit =
    A.add_final_state c.a s;
    invalidate_computations c

  let minimize
      (c:t)
    : t =
    Consts.time
      Consts.minify_times
      (fun _ ->
         let a = A.minimize c.a in
         { c with a ; up_to_date=false })

  let add_destructors
      (c:t)
    : unit =
    let all_variant_reps =
      List.dedup_and_sort
        ~compare:Type.compare
        (List.filter
           ~f:(Option.is_some % Type.destruct_variant)
           (List.map
              ~f:(fst % TypeDS.find_representative c.ds)
              c.all_types))
    in
    let conversions =
      List.map
        ~f:(fun vt ->
            let ids = List.map ~f:fst (Type.destruct_variant_exn vt) in
            let tid = Transition.VariantSwitch ids in
            let output_type = (c.output_type,TermClassification.Introduction) in
            let input_types =
              (vt,TermClassification.Elimination)::
              (List.map
                 ~f:(func_of output_type)
                 ids)
            in
            let conversion =
              fun _ vso ->
                begin match vso with
                  | (Some inv)::vso ->
                    begin match Value.node inv with
                      | Wildcard -> [Some Value.mk_wildcard]
                      | Ctor (i,v) ->
                        let index =
                          list_index_exn
                            ~equal:Id.equal
                            ids
                            i
                        in
                        [List.nth_exn vso index]
                      | _ -> failwith "ah"
                    end
                  | None::_ ->
                    [None]
                  | _ ->
                    failwith "ah"
                end
            in
            (tid,conversion,input_types,output_type))
        all_variant_reps
    in
    update_from_conversions
      c
      conversions
    (*let all_variant_reps =
      List.dedup_and_sort
        ~compare:Type.compare
        (List.filter
           ~f:(Option.is_some % Type.destruct_variant)
          (List.map
             ~f:(fst % TypeDS.find_representative c.ds)
             c.all_types))
    in
    let all_transformations =
      List.concat_map
        ~f:(fun t ->
            let all_destruct_states =
              get_states
                c
                (t,TermClassification.Elimination)
                (List.hd_exn c.inputs)
            in
            let branches =
              Type.destruct_variant_exn t
            in
            let branch_ids = List.map ~f:fst branches in
            let tid = Transition.VariantSwitch branch_ids in
            let output_intro_ct =
              (c.output_type,TermClassification.Introduction)
            in
            let all_output_type_states =
              get_states
                c
                output_intro_ct
                (List.hd_exn c.inputs)
            in
            let all_final_states =
              A.final_states c.a
            in
            List.concat_map
              ~f:(fun s ->
                  begin match s with
                    | ([i1,Some v],_) ->
                      begin match Value.node v with
                        | Ctor (vi,_) ->
                          let (vi,_) = Value.destruct_ctor_exn v in
                          let relevant_index =
                            List.find_mapi_exn
                              ~f:(fun index (bi,_) ->
                                  if Id.equal bi vi then
                                    Some index
                                  else
                                    None)
                              branches
                          in
                          let inputs_by_branches =
                            List.mapi
                              ~f:(fun i _ ->
                                  if i = relevant_index then
                                    all_final_states
                                  else
                                    all_output_type_states)
                              branches
                          in
                          let all_inputs =
                            combinations inputs_by_branches
                          in
                          List.map
                            ~f:(fun ins ->
                                (tid
                                ,s::ins
                                ,List.nth_exn ins relevant_index))
                            all_inputs
                        | Wildcard ->
                          let inputs_by_branches =
                            List.map
                              ~f:(func_of all_output_type_states)
                              branches
                          in
                          let all_inputs =
                            combinations inputs_by_branches
                          in
                          List.concat_map
                            ~f:(fun ins ->
                                let finals =
                                  List.filter
                                    ~f:(A.is_final_state c.a)
                                    ins
                                in
                                List.map
                                  ~f:(fun f ->
                                      (tid
                                      ,s::ins
                                      ,f))
                                  finals
                              )
                            all_inputs
                        | _ -> failwith "invalid"
                      end
                    | ([i1,None],_) ->
                      let inputs_by_branches =
                        List.map
                          ~f:(func_of all_output_type_states)
                          branches
                      in
                      let all_inputs =
                        combinations inputs_by_branches
                      in
                      List.map
                        ~f:(fun ins ->
                            (tid
                            ,s::ins
                            ,val_state c [(i1,None)] output_intro_ct))
                        all_inputs
                    | _ ->
                      failwith "not implemented"
                  end
                )
              all_destruct_states)
        all_variant_reps
    in
    List.iter
      ~f:(fun (t,ins,out) ->
          add_transition
            c
            t
            ins
            out
            c.output_type
            true)
      all_transformations
(*let all_transformations =
      cartesian_concat_map
        ~f:(fun (s1:State.t) (s2:State.t) ->
            begin match s1 with
              | ([i1,Some v],(t,cl)) ->
                begin match (Type.node t,cl) with
                  | (Variant branches,TermClassification.Elimination) ->
                    begin match Value.node v with
                      | Ctor (i,_) ->
                        let branch_ids = List.map ~f:fst branches in
                        begin match s2 with
                          | ([i2,_],_) ->
                            if Value.equal i1 i2 && A.is_final_state c.a s2 then
                              let ins =
                                s1::
                                List.map
                                  ~f:(fun (id,_) ->
                                      if Id.equal id i then
                                        s2
                                      else
                                        State.top)
                                  branches
                              in
                              let tid = Transition.VariantSwitch branch_ids in
                              [(tid,ins,s2)]
                            else
                              []
                          | _ -> []
                        end
                      | Wildcard ->
                        let branch_ids = List.map ~f:fst branches in
                        begin match s2 with
                          | Vals ([i2,_],_) ->
                            if Value.equal i1 i2 && A.is_final_state c.a s2 then
                              let tid = Transition.VariantSwitch branch_ids in
                              List.mapi
                                ~f:(fun i1 _ ->
                                    let ins =
                                      s1::
                                      List.mapi
                                        ~f:(fun i2 _ ->
                                            if i1 = i2 then
                                              s2
                                            else
                                              State.top)
                                        branches
                                    in
                                    (tid,ins,s2))
                                branches
                            else
                              []
                          | _ -> []
                        end
                      | _ -> failwith "no"
                    end
                  | _ -> []
                end
              | _ -> []
            end)
        (A.states c.a)
        (A.states c.a)
    in
    List.iter
      ~f:(fun (t,ins,out) ->
          add_transition
            c
            t
            ins
            out
            c.output_type
            true)
      all_transformations*)*)


  let add_states
      (c:t)
      (states:((Value.t * Value.t option) list * ClassifiedType.t) list)
    : unit =
    List.iter
      ~f:(fun (vvs,t) ->
          add_state c vvs t)
      states

  (*let recursion_targets
      (c:t)
    : State.t list =
    List.filter
      ~f:(fun s ->
          let ps = A.transitions_from c.a s in
          (not (State.equal s State.top)) &&
          List.exists
            ~f:(fun (t,ss,_) ->
                begin match (Transition.id t,ss) with
                  | (Transition.LetIn,[_;s2])
                    (*when State.equal s2 s*) ->
                    true
                  | _ -> false
                end)
            ps)
      (A.states c.a)*)

  let prune_with_recursion_intro
      c
      s =
    let ps = A.transitions_from c.a s in
    let transitions_to_prune_and_add =
      List.filter_map
        ~f:(fun tp ->
            let (t,ss,st) = tp in
            begin match (Transition.id t,ss) with
              | (Transition.LetIn,[s1;s2])
                when State.equal s s2 ->
                Some (tp,(s1,st))
              | _ -> None
            end)
        (ps)
    in
    let (prunes,adds) =
      List.unzip
        transitions_to_prune_and_add
    in
    List.iter
      ~f:(fun (t,ss,s) ->
          remove_transition
            c
            t
            ss
            s)
      prunes;
    List.iter
      ~f:(fun (sarg,target) ->
          add_transition
            c
            Transition.Rec
            [sarg]
            target
            c.output_type
            true)
      adds

  let intersect
      (c1:t)
      (c2:t)
    : t =
    print_endline @$ string_of_int (A.size c1.a);
      print_endline @$ string_of_int (A.size c2.a);
    Consts.time
      Consts.isect_times
      (fun () ->
         let merge_tset
             (c1:TransitionSet.t)
             (c2:TransitionSet.t)
           : TransitionSet.t =
           let merged = TransitionSet.union c1 c2 in
           (*let all_ts_by_id =
             group_by
               ~key:(Transition.id)
               ~equal:Transition.equal_id
               (TransitionSet.as_list merged)
           in
           List.iter
             ~f:(fun l ->
                 print_endline "here";
                 List.iter
                   ~f:(fun l -> print_endline @$ Transition.show l)
                   l;
                 assert (List.length l = 1))
             all_ts_by_id;*)
           merged
         in
         let ts =
           TransitionSet.as_list
             (merge_tset c1.tset c2.tset)
         in
         List.iter
           ~f:(update_tset c1)
           ts;
         List.iter
           ~f:(update_tset c2)
           ts;
         let ts_initial = List.filter ~f:(fun t -> Transition.arity t = 0) ts in
         let a = A.intersect ts_initial c1.a c2.a in
         let c = { c1 with a } in
         invalidate_computations c;
         c)

  (*let rec replace_all_recursions
      (c:t)
    : unit =
    let candidates =
      recursion_targets
        c
    in
    begin match candidates with
      | [] -> ()
      | h::_ ->
        prune_with_recursion_intro c h;
        replace_all_recursions
          c
    end*)

  (*let rec replace_single_recursions
      (c:t)
    : t list =
    let candidates =
      recursion_targets
        c
    in
    List.map ~f:(fun q -> let c = copy c in prune_with_recursion_intro c q; c) candidates*)

  module StateToTree = DictOf(State)(A.Term)
  module StateToTree' = DictOf(State)(PairOf(IntModule)(A.Term))
  module StateToProd = DictOf(State)(PairOf(Transition)(ListOf(State)))

  let rec term_size
      (t:A.Term.t)
    : int =
    begin match t with
      | Term (_,ts) -> List.fold_left ~f:(fun i t -> i+(term_size t)) ~init:1 ts
    end

  module ProductionPQ = PriorityQueueOf(struct
      module Priority = IntModule
      type t = int * A.Term.t * State.t
      [@@deriving eq, hash, ord, show]
      let priority = fst3
    end)

  type min_tree_acc = StateToTree.t * (Transition.t * State.t list * State.t) list
  module PQ = PriorityQueueOf(struct
      module Priority = IntModule
      type t = (int * StateToProd.t * State.t list * StateSet.t)
      let priority (i,_,_,_) = i

      let compare _ _ = failwith "no impl"
      let hash _ = failwith "no impl"
      let hash_fold_t _ _ = failwith "no impl"
      let equal _ _ = failwith "no impl"
      let pp _ _ = failwith "no impl"
      let show _ = failwith "no impl"
    end)
  type min_tree_acc' = StateToTree.t * (A.term * State.t) list

  let min_tree'
      (c:t)
    : A.term =
    let get_produced_from
        (st:StateToTree'.t)
        (t:Transition.t)
        (ss:State.t list)
      : (int * A.Term.t) option =
      let subs =
        List.map
          ~f:(fun s -> StateToTree'.lookup st s)
          ss
      in
      Option.map
        ~f:(fun iss ->
            let (ints,ss) = List.unzip iss in
            let size = List.fold ~f:(+) ~init:1 ints in
            (size,A.Term (t,ss)))
        (distribute_option subs)
    in
    let rec min_tree_internal
        (st:StateToTree'.t)
        (pq:ProductionPQ.t)
      : A.Term.t =
      begin match ProductionPQ.pop pq with
        | Some ((i,t,s),_,pq) ->
          if A.is_final_state c.a s then
            t
          else if StateToTree'.member st s then
            min_tree_internal st pq
          else
            let st = StateToTree'.insert st s (i,t) in
            let triggered_transitions = A.transitions_from c.a s in
            let produced =
              List.filter_map
                ~f:(fun (t,ss,s) ->
                    Option.map
                      ~f:(fun (i,t) -> (i,t,s))
                      (get_produced_from st t ss))
                triggered_transitions
            in
            let pq = ProductionPQ.push_all pq produced in
            min_tree_internal st pq
        | None ->
          failwith "no tree"
      end
    in
    let initial_terms =
      List.filter_map
        ~f:(fun (t,ss,s) ->
            Option.map
              ~f:(fun (i,t) -> (i,t,s))
              (get_produced_from StateToTree'.empty t ss))
        (A.transitions c.a)
    in
    min_tree_internal
      StateToTree'.empty
      (ProductionPQ.from_list initial_terms)

  let rec contains_var
      (Term (t,ts):A.Term.t)
    : bool =
    (Transition.equal_id (Transition.id t) Transition.Var)
    || (List.exists ~f:contains_var ts)

  let rec contains_rec
      (Term (t,ts):A.Term.t)
    : bool =
    (Transition.equal_id (Transition.id t) Transition.Rec)
    || (List.exists ~f:contains_rec ts)

  let rec is_valid_term
      (Term (t,ts):A.Term.t)
    : bool =
    begin match Transition.id t with
      | Rec ->
        (List.exists ~f:contains_var ts) && not (List.exists ~f:contains_rec ts)
      | VariantConstruct i ->
        begin match ts with
        | [Term (t,_)] ->
          begin match Transition.id t with
            | UnsafeVariantDestruct i' ->
            not (Id.equal i i')
          | _ -> true
          end
        | _ -> true
        end
      | _ -> true
    end

  let min_term_state
      (c:t)
    : A.TermState.t option =
    begin match c.min_term_state with
      | Some mts -> mts
      | None ->
        let mts =
          Consts.time
            Consts.min_elt_times
            (fun _ -> A.min_term_state c.a (is_valid_term % A.TermState.to_term))
        in
        c.min_term_state <- Some mts;
        mts
    end

  let size (c:t)
    : int =
    A.size c.a

  (*let accepts_term
      (c:t)
      (t:A.Term.t)
    : bool =
    Consts.time
      Consts.accepts_term_time
      (fun _ -> A.accepts_term c.a t)*)

  let size_compare
      (c1:t)
      (c2:t)
    : int =
    Int.compare (size c1) (size c2)

  let accepts_term
      (x:t)
      (term)
    : bool =
    Option.is_some (A.accepting_term_state x.a term)

  let rec_
      (c:t)
    : Transition.t =
    Transition.create (Transition.Rec, c.output_type, 1)
end
