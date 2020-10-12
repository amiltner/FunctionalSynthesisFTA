open MyStdLib

module type Symbol =
sig
  include Data
  val arity : t -> int
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

  type term = Term of Symbol.t * (term list)

  type t
  val show : t shower
  val pp : t pper
  val compare : t comparer
  val equal : t equality_check

  val empty : t
  val intersect : t -> t -> t
  val add_transition : t -> Symbol.t -> State.t list -> State.t -> t
  val remove_transition : t -> Symbol.t -> State.t list -> State.t -> t
  val states : t -> State.t list
  val final_states : t -> State.t list
  val add_final_state : t -> State.t -> t
  val is_empty : t -> bool
  val pick_term : t -> term
  val transitions_from
    : t
    -> State.t
    -> (Symbol.t * (State.t list) * State.t) list
  val minimize : t -> t
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

      module Lb = struct
        include UnitModule

        let print a b = pp b a

        let product _ _ = Some ()
      end

      include Timbuk.Automaton.Make(Symb)(St)(Lb)

      let equal a1 a2 = is_equal (compare a1 a2)
      let pp a b = print b a
    end

    type t = A.t
    [@@deriving eq, ord, show]

    module Symbol = Symbol
    module State = State

    type term = Term of Symbol.t * (term list)

    let empty = A.empty

    let intersect a1 a2 = A.inter (fun _ _ -> ()) a1 a2

    let add_transition a s sts st =
      A.add_transition
        (A.Configuration.Cons
           (s
           ,List.map
               ~f:(fun st -> A.Configuration.Var st)
               sts))
        ()
        st
        a

    let remove_transition a s sts st =
      A.remove_transition
        (A.Configuration.Cons
           (s
           ,List.map
               ~f:(fun st -> A.Configuration.Var st)
               sts))
        ()
        st
        a

    let states a =
      A.StateSet.elements
        (A.states a)

    let final_states a =
      A.StateSet.elements
        (A.final_states a)

    let add_final_state a f =
      A.add_final_state f a

    let is_empty a =
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
      c_bt bt

    let transitions_from a s =
      let ps = A.state_parents s a in
      let cs = A.ConfigurationSet.elements ps in
      List.concat_map
        ~f:(fun c ->
            let ss =
              A.LabeledStateSet.elements
                (A.states_for_configuration c a)
            in
            let (i,vs) =
              begin match c with
                | A.Configuration.Cons (i,ps) ->
                  (i
                  ,List.map
                      ~f:(fun p ->
                          begin match p with
                            | A.Configuration.Var s ->
                              s
                            | _ -> failwith "ah"
                          end)
                      ps)
                | _ ->
                  failwith "ah"
              end
            in
            List.map ~f:(fun (s,_) -> (i,vs,s)) ss)
        cs

    let minimize = A.prune_useless
  end

module Symb = struct
  type t = (Id.t * int)
  [@@deriving eq, hash, ord, show]

  let print a b = pp b a

  let arity = snd
end
