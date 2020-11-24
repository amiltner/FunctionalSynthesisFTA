open MyStdLib
open Automata


module Make : AutomatonBuilder =
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
    [@@deriving hash, eq, ord, show]

    module Term = struct
      type t = term
      [@@deriving hash, eq, ord, show]
    end

    let empty = A.empty

    let intersect a1 a2 =
      A.inter (fun _ _ -> ()) a1 a2

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

    let is_final_state a s =
      A.StateSet.mem
        s
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
        ~f:(fun (c,_) ->
            begin match c with
              | A.Configuration.Cons (i,ps) ->
                (i,
                 List.map
                   ~f:(fun p ->
                       begin match p with
                         | A.Configuration.Var s -> s
                         | _ -> failwith "shouldnt happen"
                       end)
                   ps)
              | _ -> failwith "shouldnt happen"
            end)
        (A.LabeledConfigurationSet.elements configs)

    let transitions
        (c:t)
      : (Symbol.t * (State.t list) * State.t) list =
      let sm = A.configurations_for_states c in
      let ts =
        A.StateMap.fold
          (fun s cs ts ->
             A.LabeledConfigurationSet.fold
               (fun (c,_) ts ->
                  begin match c with
                    | A.Configuration.Cons (i,ps) ->
                      (i
                      ,List.map
                          ~f:(fun p ->
                             begin match p with
                               | A.Configuration.Var s -> s
                               | _ -> failwith "shouldnt happen"
                             end)
                          ps
                      ,s)::ts
                    | _ -> failwith "shouldnt happen"
                  end)
               cs
               ts)
          sm
          []
      in
      ts

    let minimize = A.prune_useless

    let accepts_term a t =
      let rec term_to_aterm t : Symbol.t Timbuk.Term.term =
        begin match t with
          | Term (i,ts) ->
            Term (i,List.map ~f:term_to_aterm ts)
        end
      in
      A.recognizes (term_to_aterm t) a
  end
