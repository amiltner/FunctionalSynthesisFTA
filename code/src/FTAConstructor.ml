open MyStdLib
open Lang

module State =
struct
  type t =
    | Vals of (Value.t * Value.t) list * Type.t
    | Top
  [@@deriving eq, hash, ord, show]

  let destruct_vals
      (x:t)
    : ((Value.t * Value.t) list * Type.t) option =
    begin match x with
      | Vals (vs,t) -> Some (vs,t)
      | _ -> None
    end

  let destruct_vals_exn
      (x:t)
    : ((Value.t * Value.t) list * Type.t) =
    Option.value_exn (destruct_vals x)

  let top = Top

  let vals vvs t = Vals (vvs,t)

  let print a b = pp b a

  let product a b =
    begin match (a,b) with
      | (Vals (avs,at), Vals (bvs,bt)) ->
        if Type.equal at bt then
          Some (Vals ((avs@bvs),at))
        else
          None
      | (Top, _) -> Some b
      | (_, Top) -> Some a
    end
end

module Transition =
struct
  type id =
    | FunctionApp of Id.t
    | VariantConstruct of Id.t
    | UnsafeVariantDestruct of Id.t
    | TupleConstruct of int
    | TupleDestruct of int * int
    | Var
    | LetIn
    | Rec
    | VariantSwitch of Id.t list
  [@@deriving eq, hash, ord, show]
  type t_node = (id * int)
  [@@deriving eq, hash, ord, show]
  type t = t_node hash_consed
  [@@deriving eq, hash, ord, show]

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
    fst (node v)

  let print_id id =
    match id with
    | FunctionApp x -> MyStdLib.Id.to_string x
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
  let pp b (a:t) = Format.fprintf b "%s:%d " (print_id (fst a.node)) (snd a.node)
  let print a b = pp b a

  let rec_ = create (Rec,1)

  let arity = snd % node
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

  module VSet = SetOf(Value)
  module StateSet = SetOf(State)
  module InputsAndTypeToStates =
    DictOf(PairOf(ListOf(Value))(Type))(StateSet)
  module TransitionSet = SetOf(Transition)

  type t =
    {
      a                : A.t                        ;
      d                : InputsAndTypeToStates.t    ;
      ds               : TypeDS.t                   ;
      inputs           : Value.t list list          ;
      tset             : TransitionSet.t            ;
      final_candidates : Value.t -> Value.t -> bool ;
      all_types        : Type.t list                ;
      up_to_date       : bool                       ;
      input_type       : Type.t                     ;
      output_type      : Type.t                     ;
      mutable min_term_state   : A.TermState.t option option ;
    }
  [@@deriving show]

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
      | FunctionApp i ->
        List.fold
          ~f:(fun acc bt ->
              Expr.mk_app
                acc
                (term_to_exp_internals bt))
          ~init:(Expr.mk_var i)
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

  module EasyTerm = struct
    type t =
      | App of string * t list
      | VC of string * t
      | UVD of string * t
      | TC of t list
      | TD of int * int * t
      | Var
      | Rec of t
      | VSwitch of string list * t list

    let rec to_term
        (e:t)
      : A.Term.t =
      let mk_term
          (id:Transition.id)
          (children:A.Term.t list)
        : A.Term.t =
        let s = List.length children in
        A.Term (Transition.create (id,s),children)
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
    : t =
    {c with min_term_state = None}

  let get_final_values
      (c:t)
      (vin:Value.t)
    : Value.t list =
    let final_states = A.final_states c.a in
    List.concat_map
      ~f:(fun s ->
          begin match s with
            | Vals ((vinsvouts),_) ->
              List.filter_map
                ~f:(fun (vin',vout) ->
                    if Value.equal vin vin' then
                      Some vout
                    else
                      None)
                vinsvouts
            | _ -> failwith "invalid final values"
          end)
      final_states

  let get_states_singleton
      (c:t)
      (t:Type.t)
      (input:Value.t)
    : State.t list =
    StateSet.as_list
      (InputsAndTypeToStates.lookup_default
         ~default:StateSet.empty
         c.d
         ([input],get_type_rep c t))

  let get_states
      (c:t)
      (t:Type.t)
      (inputs:Value.t list)
    : State.t list =
    StateSet.as_list
      (InputsAndTypeToStates.lookup_default
         ~default:StateSet.empty
         c.d
         (inputs,get_type_rep c t))

  let top_state : State.t = State.top

  let val_state
      (c:t)
      (vinsvouts:(Value.t * Value.t) list)
      (t:Type.t)
    : State.t =
    let t = get_type_rep c t in
    State.vals vinsvouts t

  let add_state
      (c:t)
      (vinsvouts:(Value.t * Value.t) list)
      (t:Type.t)
    : t =
    let t = get_type_rep c t in
    let vins = List.map ~f:fst vinsvouts in
    let s = val_state c vinsvouts t in
    let d =
      InputsAndTypeToStates.insert_or_combine
        ~combiner:(StateSet.union)
        c.d
        (vins,t)
        (StateSet.singleton s)
    in
    let _ = InputsAndTypeToStates.lookup_exn d (vins,t) in
    let c =
      if Type.equal t c.output_type
      && List.for_all ~f:(uncurry c.final_candidates) vinsvouts then
        let a = A.add_final_state c.a s in
        {c with a}
      else
        c
    in
    invalidate_computations {c with d}

  let update_tset
      (c:t)
      (trans:Transition.t)
    : t =
    if TransitionSet.member c.tset trans then
      c
    else
      let a =
        A.add_transition
          c.a
          trans
          (List.init ~f:(func_of State.top) (Transition.arity trans))
          State.top
      in
      let tset = TransitionSet.insert trans c.tset in
      invalidate_computations { c with a ; tset ; }


  let add_transition
      (c:t)
      (trans_id:Transition.id)
      (sins:State.t list)
      (sout:State.t)
      (ensure_state:bool)
    : t =
    let c =
      update_tset
        c
        (Transition.create (trans_id,List.length sins))
    in
    if ensure_state then
      let c =
        begin match sout with
          | Top -> c
          | Vals (vinsvouts,t) ->
            add_state c vinsvouts t
        end
      in
      let a =
        A.add_transition
          c.a
          (Transition.create (trans_id,List.length sins))
          sins
          sout
      in
      invalidate_computations { c with a }
    else if A.has_state c.a sout then
      let a =
        A.add_transition
          c.a
          (Transition.create (trans_id,List.length sins))
          sins
          sout
      in
      invalidate_computations { c with a }
    else
      c

  let remove_transition
      (c:t)
      (trans:Transition.t)
      (sins:State.t list)
      (sout:State.t)
    : t =
    invalidate_computations {c with
     a = A.remove_transition c.a trans sins sout }

  let evaluate
      (c:t)
      (input:Value.t list)
      (f:Value.t list -> Value.t list)
      (args:State.t list)
      (t:Type.t)
    : State.t list =
    let vs = List.map ~f:State.destruct_vals_exn args in
    let vs = List.map ~f:(List.map ~f:snd % fst) vs in
    let args =
      begin match vs with
        | [] -> List.init ~f:(func_of []) (List.length input)
        | _ -> List.transpose_exn vs
      end
    in
    let outos = List.map ~f args in
    let outsl = List.transpose_exn outos in
    List.map
      ~f:(fun outs ->
          let in_outs = List.zip_exn input outs in
          val_state c in_outs t)
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

  let update_from_conversions
      ?(ensure_state:bool = true)
      (c:t)
      (conversions:(Transition.id
                    * (Value.t list -> Value.t list)
                    * (Type.t list) * Type.t) list)
    : t =
    let ids_ins_outs =
      List.concat_map
        ~f:(fun (i,e,tins,tout) ->
            List.concat_map
              ~f:(fun input ->
                  let args_choices =
                    List.map
                      ~f:(fun t -> get_states c t input)
                      tins
                  in
                  let args_list =
                    combinations
                      args_choices
                  in
                  List.concat_map
                    ~f:(fun ins ->
                        let outs = evaluate c input e ins tout in
                        List.map
                          ~f:(fun out -> (i,ins,out))
                          outs)
                    args_list)
              c.inputs)
        conversions
    in
    List.fold
      ~f:(fun a (i,ins,out) ->
          add_transition
            a
            i
            ins
            out
            ensure_state)
      ~init:c
      ids_ins_outs

  let create_ds_from_t_list_context
      ~(context:Context.t)
      (ts:Type.t list)
    : TypeDS.t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.filter
           ~f:(Option.is_none % Type.destruct_arr)
           (List.concat_map
              ~f:(Typecheck.all_subtypes context.tc)
              ts))

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
        (List.filter
           ~f:(Option.is_none % Type.destruct_arr)
           (List.concat_map
              ~f:(Typecheck.all_subtypes problem.tc)
              ts))

    in
    TypeDS.create_from_list
      ~equiv:(Typecheck.type_equiv problem.tc)
      all_types

  let initialize_context
      ~(context:Context.t)
      (ts:Type.t list)
      (inputs:Value.t list)
      ((input_type,output_type):Type.t * Type.t)
      (final_candidates:Value.t -> Value.t -> bool)
    : t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.filter
           ~f:(Option.is_none % Type.destruct_arr)
           (List.concat_map
              ~f:(Typecheck.all_subtypes context.tc)
              ts))

    in
    let ds = create_ds_from_t_list_context ~context ts in
    let a = A.empty in
    let d = InputsAndTypeToStates.empty in
    let input_vals = inputs in
    let inputs = List.map ~f:(fun i -> [i]) inputs in
    let tset = TransitionSet.empty in
    let (input_type,_) = TypeDS.find_representative ds input_type in
    let (output_type,_) = TypeDS.find_representative ds output_type in
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
      }
    in
    List.fold
      ~f:(fun c i ->
          add_transition
            c
            Var
            []
            (val_state c [(i,i)] input_type)
            true)
      ~init:c
      input_vals

  let initialize
      ~(problem:Problem.t)
      (ts:Type.t list)
      (inputs:Value.t list)
      ((input_type,output_type):Type.t * Type.t)
      (final_candidates:Value.t -> Value.t -> bool)
    : t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.filter
           ~f:(Option.is_none % Type.destruct_arr)
           (List.concat_map
              ~f:(Typecheck.all_subtypes problem.tc)
              ts))

    in
    let ds = create_ds_from_t_list ~problem ts in
    let a = A.empty in
    let d = InputsAndTypeToStates.empty in
    let input_vals = inputs in
    let inputs = List.map ~f:(fun i -> [i]) inputs in
    let tset = TransitionSet.empty in
    let (input_type,_) = TypeDS.find_representative ds input_type in
    let (output_type,_) = TypeDS.find_representative ds output_type in
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
      }
    in
    List.fold
      ~f:(fun c i ->
          add_transition
            c
            Var
            []
            (val_state c [(i,i)] input_type)
            true)
      ~init:c
      input_vals

  let get_all_types
      (c:t)
    : Type.t list =
    c.all_types

  let add_let_ins
      (c:t)
    : t =
    List.fold
      ~f:(fun c (s1,s2) ->
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
                 c
            | _ -> c
          end)
      ~init:c
      (List.cartesian_product (A.states c.a) (A.states c.a))

  let add_final_state
      (c:t)
      (s:State.t)
    : t =
    let a = A.add_final_state c.a s in
    invalidate_computations { c with a }

  let minimize
      (c:t)
    : t =
    Consts.time
      Consts.minify_time
      (fun _ -> 
         let a = A.minimize c.a in
         { c with a ; up_to_date=false })

  let add_destructors
      (c:t)
    : t =
    let all_transformations =
      cartesian_filter_map
        ~f:(fun (s1:State.t) (s2:State.t) ->
            begin match s1 with
              | Vals ([i1,v],t) ->
                begin match Type.node t with
                  | Variant branches ->
                    begin match Value.node v with
                      | Ctor (i,_) ->
                        let branch_ids = List.map ~f:fst branches in
                        begin match s2 with
                          | Vals ([i2,_],_) ->
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
                              Some (tid,ins,s2)
                            else
                              None
                          | _ -> None
                        end
                      | _ -> None
                    end
                  | _ -> None
                end
              | _ -> None
            end)
        (A.states c.a)
        (A.states c.a)
    in
    List.fold
      ~f:(fun c (t,ins,out) ->
          add_transition
            c
            t
            ins
            out
            true)
      ~init:c
      all_transformations


  let add_states
      (c:t)
      (states:((Value.t * Value.t) list * Type.t) list)
    : t =
    List.fold
      ~f:(fun c (vvs,t) ->
          add_state c vvs t)
      ~init:c
      states

  let recursion_targets
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
      (A.states c.a)

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
    let c =
      List.fold
        ~f:(fun c (t,ss,s) ->
            remove_transition
              c
              t
              ss
              s)
        ~init:c
        prunes
    in
    let c =
      List.fold
        ~f:(fun c (sarg,target) ->
            add_transition
              c
              Transition.Rec
              [sarg]
              target
              true)
        ~init:c
        adds
    in
    c

  let intersect
      (c1:t)
      (c2:t)
    : t =
    Consts.time
      Consts.isect_time
      (fun () ->
         let merge_tset
             (c1:TransitionSet.t)
             (c2:TransitionSet.t)
           : TransitionSet.t =
           let merged = TransitionSet.union c1 c2 in
           let all_ts_by_id =
             group_by
               ~key:(Transition.id)
               ~equal:Transition.equal_id
               (TransitionSet.as_list merged)
           in
           List.iter
             ~f:(fun l -> assert (List.length l = 1))
             all_ts_by_id;
           merged
         in
         let ts =
           TransitionSet.as_list
             (merge_tset c1.tset c2.tset)
         in
         let c1 =
           List.fold
             ~f:update_tset
             ~init:c1
             ts
         in
         let c2 =
           List.fold
             ~f:update_tset
             ~init:c2
             ts
         in
         let a = A.intersect c1.a c2.a in
         invalidate_computations { c1 with a ; up_to_date = false ; })

  let rec replace_all_recursions
      (c:t)
    : t =
    let candidates =
      recursion_targets
        c
    in
    begin match candidates with
      | [] -> c
      | h::_ ->
        replace_all_recursions
          (prune_with_recursion_intro c h)
    end

  let rec replace_single_recursions
      (c:t)
    : t list =
    let candidates =
      recursion_targets
        c
    in
    List.map ~f:(prune_with_recursion_intro c) candidates

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
      [@@deriving eq, hash, ord, show]
      let priority (i,_,_,_) = i
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

  let min_term_state
      (c:t)
    : A.TermState.t option =
    begin match c.min_term_state with
      | Some mts -> mts
      | None ->
        let mts =
          Consts.time
            Consts.min_elt_time
            (fun _ -> A.min_term_state c.a)
        in
        c.min_term_state <- Some mts;
        mts
    end

  let size (c:t)
    : int =
    A.size c.a

  let accepts_term
      (c:t)
      (t:A.Term.t)
    : bool =
    Consts.time
      Consts.accepts_term_time
      (fun _ -> A.accepts_term c.a t)

  let size_compare
      (c1:t)
      (c2:t)
    : int =
    Int.compare (size c1) (size c2)
end
