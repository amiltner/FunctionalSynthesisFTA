open MyStdLib

module type Symbol =
sig
  include Data
  val arity : t -> int
  val cost : t -> int
end

module type State =
sig
  include Data
  val product : t -> t -> t option
end

module type Automaton =
sig
  module Symbol : Symbol
  module State : State

  type term =  Term of Symbol.t * (term list)
  module Term : sig
    include Data with type t = term
  end

  type term_state = TS of Symbol.t * State.t * term_state list
  module TermState :
  sig
    include Data with type t = term_state

    val to_term : t -> term

    val get_state : t -> State.t
  end

  type t
  val show : t shower
  val pp : t pper
  val compare : t comparer
  val equal : t equality_check

  val empty : unit -> t
  val intersect : Symbol.t list -> t -> t -> t
  val copy : t -> t
  val add_transition : t -> Symbol.t -> State.t list -> State.t -> unit
  val remove_transition : t -> Symbol.t -> State.t list -> State.t -> unit
  val states : t -> State.t list
  val final_states : t -> State.t list
  val is_final_state : t -> State.t -> bool
  val add_final_state : t -> State.t -> unit
  val has_state : t -> State.t -> bool
  (*val is_empty : t -> bool*)
  (*val accepts_term : t -> Term.t -> bool*)
  val accepting_term_state : t -> Term.t -> TermState.t option
  val transitions_from
    : t
    -> State.t
    -> (Symbol.t * (State.t list) * State.t) list
  val transitions_to : t -> State.t -> (Symbol.t * (State.t list)) list
  val transitions : t -> (Symbol.t * (State.t list) * State.t) list
  val minimize : t -> t
  val size : t -> int
  val min_term_state : t -> (term -> bool) -> (term -> Float.t) -> term_state option
end

module type AutomatonBuilder =
  functor (Symbol : Symbol) ->
  functor (State : State) ->
    Automaton with module Symbol := Symbol
               and module State := State

module TimbukBuilder : AutomatonBuilder =
  functor (Symbol : Symbol) ->
  functor (State : State) ->
  struct
    (* A is the timbuk automaton module *)
    module A =
    struct
      module Symb =
      struct
        include Symbol

        let print a b = pp b a
      end

      module St =
      struct
        include State

        let print a b = pp b a
      end

      include Timbuk.Automaton.Make(Symb)(St)

      let equal a1 a2 = is_equal (compare a1 a2)
      let pp a b = print b a
    end

    type t = A.t
    [@@deriving eq, ord, show]

    module Symbol = Symbol
    module State = State

    type term = Term of Symbol.t * (term list)
    [@@deriving hash, eq, ord, show]

    module Term = struct
      type t = term
      [@@deriving hash, eq, ord, show]
    end

    type term_state = TS of Symbol.t * State.t * term_state list
    [@@deriving hash, eq, ord, show]

    module TermState =
    struct
      type t = term_state
      [@@deriving eq, hash, ord, show]

      let rec to_term
          (TS (t,_,tss):t)
        : Term.t =
        Term (t,List.map ~f:to_term tss)

      let get_state
          (TS (_,s,tss):t)
        : State.t =
        s
    end

    let empty = A.empty

    let copy = A.copy

    let intersect s a1 a2 =
      A.inter s a1 a2

    let add_transition a s sts st =
      A.add_transition
        (A.Configuration.create (
           (s
           ,
               sts)))
        st
        a

    let remove_transition a s sts st =
      A.remove_transition
        (A.Configuration.create (
           (s
           ,
               sts)))
        st
        a

    let states a =
      A.StateSet.as_list
        (A.states a)

    let final_states a =
      A.StateSet.as_list
        (A.final_states a)

    let is_final_state a s =
      A.StateSet.contains
        s
        (A.final_states a)

    let add_final_state a f =
      A.add_final_state f a

    let has_state
        a
        s
      =
      A.StateSet.contains s (A.states a)

    (*let is_empty a =
      Option.is_some
        (A.pick_term_opt
           a)

    let pick_term a =
      let bt =
        Option.value_exn
          (A.pick_term_opt
             a)
      in
      let rec c_bt
          ((bt,_):A.BoundTerm.t)
        : term =
        begin match bt with
          | A.BoundTerm.Term (s,bts) ->
            let ts = List.map ~f:c_bt bts in
            Term (s,ts)
          | _ -> failwith "ah"
        end
      in
      c_bt bt*)

    let transitions_from a s =
      let ps = A.state_parents s a in
      let cs = A.ConfigurationSet.as_list ps in
      List.concat_map
        ~f:(fun c ->
            let ss =
              A.StateSet.as_list
                (A.states_for_configuration c a)
            in
            let (i,vs) = A.Configuration.node c in
            List.map ~f:(fun s -> (i,vs,s)) ss)
        cs

    let transitions_to
        a
        s
      : (Symbol.t * (State.t list)) list =
      let configs =
        A.configurations_for_state
          s
          a
      in
      List.map
        ~f:(fun c ->
            A.Configuration.node c)
        (A.ConfigurationSet.as_list configs)

    let transitions
        (c:t)
      : (Symbol.t * (State.t list) * State.t) list =
      let sm = A.configurations_for_states c in
      let ts =
        A.StateMap.fold
          (fun s cs ts ->
             A.ConfigurationSet.fold
               (fun c ts ->
                  let (i,ss) = (A.Configuration.node c) in
                  (i,ss ,s)::ts)
               cs
               ts)
          sm
          []
      in
      ts

    let minimize = A.prune_useless

    let size = A.state_count

    (*let accepts_term a t =
      let rec term_to_aterm t : Symbol.t Timbuk.Term.term =
        begin match t with
          | Term (i,ts) ->
            Term (i,List.map ~f:term_to_aterm ts)
        end
      in
      A.recognizes (term_to_aterm t) a*)

    module StateToTS = DictOf(State)(PairOf(FloatModule)(TermState))
    module TSPQ = PriorityQueueOf(struct
        module Priority = FloatModule
        type t = Float.t * TermState.t * State.t
        [@@deriving eq, hash, ord, show]
        let priority = fst3
      end)
    let min_term_state
        (a:t)
        (f:Term.t -> bool)
        (cost:Term.t -> Float.t)
      : TermState.t option =
      let get_produced_from
          (st:StateToTS.t)
          (t:Symbol.t)
          (s:State.t)
          (ss:State.t list)
        : (Float.t * TermState.t) option =
        let subs =
          List.map
            ~f:(fun s -> StateToTS.lookup st s)
            ss
        in
        Option.map
          ~f:(fun iss ->
              let (ints,ss) = List.unzip iss in
              let ts = TS (t,s,ss) in
              let term = TermState.to_term ts in
              let size = cost term in
              (size,TS (t,s,ss)))
          (distribute_option subs)
      in
      let rec min_tree_internal
          (st:StateToTS.t)
          (pq:TSPQ.t)
        : TermState.t option =
        begin match TSPQ.pop pq with
          | Some ((c,t,s),_,pq) ->
            if f (TermState.to_term t) then
              if is_final_state a s then
                begin
                  (*print_endline (Float.to_string c);*)
                  Some t
                end
              else if StateToTS.member st s then
                min_tree_internal st pq
              else
                let st = StateToTS.insert st s (c,t) in
                let triggered_transitions = transitions_from a s in
                let produced =
                  List.filter_map
                    ~f:(fun (t,ss,s) ->
                        Option.map
                          ~f:(fun (i,t) -> (i,t,s))
                          (get_produced_from st t s ss))
                    triggered_transitions
                in
                let pq = TSPQ.push_all pq produced in
                min_tree_internal st pq
            else
              min_tree_internal st pq
          | None -> None
        end
      in
      let initial_terms =
        List.filter_map
          ~f:(fun (t,ss,s) ->
              Option.map
                ~f:(fun (i,t) -> (i,t,s))
                (get_produced_from StateToTS.empty t s ss))
          (transitions a)
      in
      min_tree_internal
        StateToTS.empty
        (TSPQ.from_list initial_terms)

    let accepting_term_state (a:t) (t:term) : TermState.t option =
      let rec accepting_term_state_state t q =
        begin match t with
          | Term (i,ts) ->
            List.find_map
              ~f:(fun (i',ss) ->
                  if Symbol.equal i i' then
                    let ts_ss = List.zip_exn ts ss in
                    Option.map
                      ~f:(fun ts -> TS (i,q,ts))
                      (distribute_option
                         (List.map
                            ~f:(uncurry accepting_term_state_state)
                            ts_ss))
                  else
                    None)
              (transitions_to a q)
        end
      in
      List.find_map ~f:(accepting_term_state_state t) (final_states a)
  end
