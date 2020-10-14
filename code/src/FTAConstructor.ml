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
  type t = (Id.t * int)
  [@@deriving eq, hash, ord, show]

  let print a b = pp b a

  let arity = snd
end

module Make(A : Automata.Automaton with module Symbol := Transition and module State := State) = struct
  module TypeDS =
    DisjointSetWithSetDataOf
      (Type)
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
    }

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
    let vins = List.map ~f:fst vinsvouts in
    let d =
      InputsAndTypeToStates.insert_or_combine
        ~combiner:(StateSet.union)
        c.d
        (vins,t)
        (StateSet.singleton (val_state c vinsvouts t))
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
      (trans_id:Id.t)
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

  let evaluate
      (c:t)
      (input:Value.t list)
      (e:Expr.t)
      (args:State.t list)
      (t:Type.t)
    : State.t =
    let vs = List.map ~f:State.destruct_vals_exn args in
    let vs = List.map ~f:(List.map ~f:snd % fst) vs in
    let args =
      begin match vs with
        | [] -> List.init ~f:(func_of []) (List.length input)
        | _ -> List.transpose_exn vs
      end
    in
    let args =
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
    let outs = List.map ~f:Eval.evaluate full_exps in
    let in_outs = List.zip_exn input outs in
    val_state c in_outs t

  let update_from_conversions
      (c:t)
      (conversions:(Id.t * Expr.t * (Type.t list) * Type.t) list)
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
                  List.map
                    ~f:(fun ins ->
                        (i,ins,evaluate c input e ins tout))
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
      (input_type:Type.t)
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
    let c =
      {
        a                ;
        d                ;
        ds               ;
        inputs           ;
        tset             ;
        final_candidates ;
      }
    in
    List.fold
      ~f:(fun c i ->
          add_transition
            c
            (Id.create "x")
            []
            (val_state c [(i,i)] input_type))
      ~init:c
      input_vals

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
                  (Id.create "let-in")
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
    let a = A.minimize c.a in
    { c with a }

  let add_destructors
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
                  (Id.create "ifthenelse")
                  [(val_state c [(i,Value.true_val)] Type._bool)
                  ;s
                  ;State.top]
                  s
              in
              let c =
                add_transition
                  c
                  (Id.create "ifthenelse")
                  [(val_state c [(i,Value.false_val)] Type._bool)
                  ;State.top
                  ;s]
                  s
              in
              c
            | _ -> failwith "invalid"
          end)
      ~init:c
      (A.states c.a)

  let add_states
      (c:t)
      (states:((Value.t * Value.t) list * Type.t) list)
    : t =
    List.fold
      ~f:(fun c (vvs,t) ->
          add_state c vvs t)
      ~init:c
      states
end
