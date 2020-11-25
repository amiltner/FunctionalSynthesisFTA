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

  type term =  Term of Symbol.t * (term list)
  module Term : sig
    include Data with type t = term
  end

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
  val is_final_state : t -> State.t -> bool
  val add_final_state : t -> State.t -> t
  val is_empty : t -> bool
  val pick_term : t -> Term.t
  val accepts_term : t -> Term.t -> bool
  val transitions_from
    : t
    -> State.t
    -> (Symbol.t * (State.t list) * State.t) list
  val transitions_to : t -> State.t -> (Symbol.t * (State.t list)) list
  val transitions : t -> (Symbol.t * (State.t list) * State.t) list
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
    [@@deriving hash, eq, ord, show]

    module Term = struct
      type t = term
      [@@deriving hash, eq, ord, show]
    end

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

module VATABuilder : AutomatonBuilder =
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
      let s1 = A.states a1 in
      let prints s = Format.printf "%t\n" (A.State.print s) in
      (*let _ = A.StateSet.iter prints s1; print_endline "\n" in*)
      let alpha1 = A.alphabet a1 in
      let printa a = (*Format.printf "%t " (A.Sym.print a) in*)
        A.Sym.print a Format.str_formatter in
      (*let _ = A.SymSet.iter printa alpha1; print_endline (Format.flush_str_formatter ()); print_endline "\n" in*)
      (*let aa1 = A.pp Format.std_formatter a1; print_endline "\n" in*)
      let fold c l s a =
        match c with
        | A.Configuration.Cons (x, y) -> a
        | A.Configuration.Var x -> a in
      let b1 = TimbukSpec.Spec.Automata.empty in
      let x1 = TimbukSpec.Spec.Aut.create () in
      let t1 = A.fold_transitions fold a1 x1 in
      let x1 = TimbukSpec.Spec.Aut.add_transition
          (TimbukSpec.Spec.Aut.Configuration.Cons
             (TimbukTyping.AppSymbol.Sym (Timbuk.StringSymbol.create "f" 1),
              [TimbukSpec.Spec.Aut.Configuration.Var(TimbukTyping.GenericTypes.PolyBase (TimbukSpec.UserState.of_string "a"))])) ()
          (TimbukTyping.GenericTypes.PolyBase (TimbukSpec.UserState.of_string "b")) x1 in
      (*let al1 = TimbukSpec.Spec.Alphabet.empty in*)
      let span x = Codemap.Span.located Codemap.Span.default x in
      (*let al1 = TimbukSpec.Spec.Alphabet.add "A" (span (TimbukTyping.AppSymbol.Sym (Timbuk.StringSymbol.create "f" 1))) al1 in*)
      let loc = span x1 in
      let b1 = TimbukSpec.Spec.Automata.add "A1" loc b1 in
      let _ = A.SymSet.iter printa alpha1 in
      (*; print_endline (Format.flush_str_formatter ()); print_endline "\n" in*)
      let _ = Format.printf "Ops %s\n\n%t\n"
          (Format.flush_str_formatter ())
          (*(TimbukSpec.Spec.Alphabet.print al1)*)
          (TimbukSpec.Spec.Automata.print b1) in
      let _ = A.SymSet.iter printa alpha1 in
      let al1 = Format.flush_str_formatter () in
      let str1 = "Ops " ^
                 al1 ^
                 (*(print_to_string TimbukSpec.Spec.Alphabet.print al1) ^**)
                 "\n\n" ^
                 (print_to_string TimbukSpec.Spec.Automata.print b1) ^ "\n" in
      (*let _ = print_endline (print_to_string TimbukSpec.Spec.Automata.print b1)
        print_endline (print_to_string TimbukSpec.Spec.Aut.print x1) in*)
      (*let x1 = TimbukSpec.Spec.Aut.add_transition TimbukSpec.Spec.Aut.Configuration.Var () q x1 in*)
      SimpleFile.write_to_file
        ~fname:"/tmp/a1.timbuk"
        ~contents:(*(print_to_string A.print a1)*)str1;
      SimpleFile.write_to_file
        ~fname:"/tmp/a2.timbuk"
        ~contents:(print_to_string A.print a2);
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
