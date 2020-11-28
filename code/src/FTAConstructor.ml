open MyStdLib

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
    | TupleConstruct of Type.t
    | TupleDestruct of Type.t * int
    | Var
    | LetIn
    | Rec
    | IfThenElse (* TODO change to variant-switch *)
    | VariantSwitch of Id.t list (* TODO remove *)
  [@@deriving eq, hash, ord, show]
  type t = (id * int)
  [@@deriving eq, hash, ord, show]

  let print_id id =
    match id with
    | FunctionApp x -> MyStdLib.Id.to_string x
    | VariantConstruct x -> MyStdLib.Id.to_string x
    | TupleConstruct _ -> "TupleConstruct"
    | Var -> "Var"
    | LetIn -> "LetIn"
    | Rec -> "Rec"
    | IfThenElse -> "IfThenElse"
    | _ -> "other"
  let pp b (a:t) = Format.fprintf b "%s:%d " (print_id (fst a)) (snd a)
  let print a b = pp b a

  let rec_ = (Rec,1)

  let arity = snd
end

module Make(A : Automata.Automaton with module Symbol := Transition and module State := State) = struct
  module TypeDS =
    DisjointSetWithSetDataOf
      (struct
        include Type
        let preferred t1 t2 =
          begin match t1 with
            | Variant _
            | Arrow _
            | Tuple _ -> true
            | _ -> false
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
    {c with d}

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
      { c with a ; tset ; }


  let add_transition
      (c:t)
      (trans_id:Transition.id)
      (sins:State.t list)
      (sout:State.t)
    : t =
    let c =
      update_tset
        c
        (trans_id,List.length sins)
    in
    let c =
      begin match sout with
        | Top -> c
        | Vals (vinsvouts,t) ->
          add_state c vinsvouts t
      end
    in
    let a = A.add_transition c.a (trans_id,List.length sins) sins sout in
    {c with a}


  let remove_transition
      (c:t)
      (trans:Transition.t)
      (sins:State.t list)
      (sout:State.t)
    : t =
    {c with
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
            out)
      ~init:c
      ids_ins_outs

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
    let ds =
      TypeDS.create_from_list
        ~equiv:(Typecheck.type_equiv problem.tc)
        all_types
    in
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
            (val_state c [(i,i)] input_type))
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
    { c with a }

  let minimize
      (c:t)
    : t =
    Consts.time
      Consts.minify_time
      (fun _ -> 
         let a = A.minimize c.a in
         { c with a ; up_to_date=false })

  let add_ite
      (c:t)
    : t =
    List.fold
      ~f:(fun c s ->
          begin match s with
            | Top -> c
            | Vals ([(i,_)],_) ->
              let c =
                add_transition
                  c
                  IfThenElse
                  [(val_state c [(i,Value.true_)] Type._bool)
                  ;s
                  ;State.top]
                  s
              in
              let c =
                add_transition
                  c
                  IfThenElse
                  [(val_state c [(i,Value.false_)] Type._bool)
                  ;State.top
                  ;s]
                  s
              in
              c
            | _ -> failwith "invalid"
          end)
      ~init:c
      (A.states c.a)

  let add_destructors
      (c:t)
    : t =
    let all_transformations =
      cartesian_filter_map
        ~f:(fun (s1:State.t) (s2:State.t) ->
            begin match s1 with
              | Vals ([i1,Ctor (i,_)],Variant branches) ->
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
            out)
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
                begin match (t,ss) with
                  | ((Transition.LetIn,_),[_;s2])
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
            let ((t,_),ss,st) = tp in
            begin match (t,ss) with
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
              target)
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
               ~key:fst
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
         { c1 with a ; up_to_date = false ; })

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
    Consts.time
      Consts.min_elt_time
      (fun _ -> A.min_term_state c.a)

  let min_tree
      (c:t)
    : A.term =
    let update_sts
        (st:StateToTree.t)
        ((i,ss,t):Transition.t * State.t list * State.t)
        ((acc_st,acc_new_trans):min_tree_acc)
      : (min_tree_acc,A.Term.t) either =
      if StateToTree.member st t then
        Left (acc_st,acc_new_trans)
      else
        let subs =
          List.map
            ~f:(fun s -> StateToTree.lookup st s)
            ss
        in
        begin match distribute_option subs with
          | None -> Left (acc_st,acc_new_trans)
          | Some sts ->
            let term = A.Term (i,sts) in
            if A.is_final_state c.a t then
              Right term
            else
              let acc_st =
                StateToTree.insert_or_combine
                  ~combiner:(fun v1 v2 -> if term_size v1 < term_size v2 then v1 else v2)
                  acc_st
                  t
                  term
              in
              let acc_new_trans = acc_new_trans@(A.transitions_from c.a t) in
              Left (acc_st,acc_new_trans)
        end
    in
    let process_boundary
        (st:StateToTree.t)
        (boundary:(Transition.t * State.t list * State.t) list)
      : (StateToTree.t * (Transition.t * State.t list * State.t) list,A.Term.t) either =
      let rec process_boundary_internal
          (st:StateToTree.t)
          (boundary:(Transition.t * State.t list * State.t) list)
          (acc:min_tree_acc)
        : (min_tree_acc,A.Term.t) either =
        begin match boundary with
          | [] -> Left acc
          | h::t ->
            begin match update_sts st h acc with
              | Left acc -> process_boundary_internal st t acc
              | Right t1 as racc ->
                let remaining_smallest = process_boundary_internal st t acc in
                begin match remaining_smallest with
                  | Left _ -> racc
                  | Right t2 -> if term_size t1 < term_size t2 then Right t1 else Right t2
                end
            end
        end
      in
      process_boundary_internal st boundary (st,[])
    in
    fold_until_completion
      ~f:(fun (st,boundary) ->
          begin match boundary with
            | [] -> failwith "no boundary"
            | _ -> process_boundary st boundary
          end)
      (StateToTree.empty,A.transitions c.a)

  let size (c:t)
    : int =
    A.size c.a

  let min_term_state
      (c:t)
    : A.TermState.t option =
    begin match c.min_term_state with
      | Some ts -> ts
      | None ->
        let mts = A.min_term_state c.a in
        c.min_term_state <- Some mts;
        mts
    end

  let accepts_term
      (c:t)
      (t:A.Term.t)
    : bool =
    A.accepts_term c.a t
end
