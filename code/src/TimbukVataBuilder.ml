open MyStdLib
open Automata


module Make : AutomatonBuilder =
  functor (Symbol : Symbol) ->
  functor (State : State) ->
  struct
    module TimbukAut = TimbukBuilder(Symbol)(State)

    type term = Term of Symbol.t * (term list)
    [@@deriving hash, eq, ord, show]

    module Term = struct
      type t = term
      [@@deriving hash, eq, ord, show]
    end

    let rec to_timbuk_term
        (x:term)
      : TimbukAut.term =
      begin match x with
        | Term (s,ts) -> TimbukAut.Term (s,List.map ~f:to_timbuk_term ts)
      end

    type term_state = TS of Symbol.t * State.t * term_state list
    [@@deriving hash, eq, ord, show]

    let rec from_timbuk_termstate
        (x:TimbukAut.TermState.t)
      : term_state =
      begin match x with
        | TS (sy,s,tss) -> TS (sy,s,List.map ~f:from_timbuk_termstate tss)
      end

    let rec from_timbuk_term
        (x:TimbukAut.Term.t)
      : term =
      begin match x with
        | Term (sy,tss) -> Term (sy,List.map ~f:from_timbuk_term tss)
      end

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

    type t =
      {
        mutable aut   : TimbukAut.t option ;
        mutable fname : string      option ;
      }
    [@@deriving eq, ord, show]

    let create_from_timbuk
        (x:TimbukAut.t)
      : t =
      {
        aut   = Some x ;
        fname = None   ;
      }

    let create_from_fname
        (f:string)
      : t =
      {
        aut   = None   ;
        fname = Some f ;
      }

    module SB = IdentifierBijection.Make(State)
        (struct
          let num = ref 0
          let fresh _ =
            let n = !num in
            incr num;
            Id.create ("s" ^ (string_of_int n))
        end)
        (struct
          type t = string
          let value = "auts/state_bijection.mapping"
        end)
    module TB = IdentifierBijection.Make(Symbol)(struct
        let num = ref 0
        let fresh _ =
          let n = !num in
          incr num;
          Id.create ("t" ^ (string_of_int n))
      end)
        (struct
          type t = string
          let value = "auts/symbol_bijection.mapping"
        end)

    let empty () = create_from_timbuk (TimbukAut.empty ())

    module ASTBuilder =
    struct
      module Ast =  TimbukSpec.Ast

      let state_from_str
          (id:string)
        : State.t option =
        let stripped =
          String.strip
            ~drop:(fun c -> Char.equal '[' c || Char.equal ']' c)
            id
        in
        let individual_components =
          String.split
            ~on:'|'
            stripped
        in
        let cleaned_components =
          List.map
            ~f:(fun comp ->
                Id.create
                  (List.hd_exn
                     (String.split
                        ~on:'_'
                        comp)))
            individual_components
        in
        let components =
          List.map
            ~f:SB.get_d
            cleaned_components
        in
        begin match components with
          | [] -> failwith "shouldnt occur"
          | h::t ->
            List.fold
              ~f:(fun acc x ->
                  begin match acc with
                    | None -> None
                    | Some acc -> State.product acc x
                  end)
              ~init:(Some h)
              t
        end

      let symbol_from_str
          (id:string)
        : Symbol.t =
        let id = Id.create id in
        TB.get_d id

      let final_states (ast, _) =

        let state (ast, _) =
          state_from_str (fst ast.Ast.state_name)
        in
        List.map ~f:(
          fun ast ->
            let s = state ast in
              s
        )
          ast

      let config_state (ast,span) =
        let id, _ = ast.Ast.term_cons in
        state_from_str id

      let configuration (ast,span) =
        let id, id_span = ast.Ast.term_cons in
        let subs = List.map ~f:(config_state) (fst ast.Ast.term_subs) in
        let sym = symbol_from_str id in
        (sym,subs)

      let transitions (ast, span) =
        List.fold_left
          ~f:(fun rules (rule, span) ->
              let (sym,subs) = configuration rule.Ast.rule_left in
              let out = config_state rule.Ast.rule_right in
              (sym,subs,out)::rules)
          ~init:[]
          ast

      let automaton (ast, _) =
        let roots = final_states ast.Ast.aut_roots in
        let aut = TimbukAut.empty () in
        List.iter
          ~f:(TimbukAut.add_final_state aut)
          (List.filter_map ~f:ident roots);
        let transitions = transitions ast.Ast.aut_transitions in
        List.iter
          ~f:(fun (sym,subs,out) ->
              begin match (distribute_option subs,out) with
                | (Some subs, Some out) ->
                  TimbukAut.add_transition
                    aut
                    sym
                    subs
                    out
                | _ ->
                  ()
              end)
          transitions;
        aut
    end

    let get_aut
        (x:t)
      : TimbukAut.t =
      begin match x.aut with
        | Some aut -> aut
        | None ->
          let fname = Option.value_exn x.fname in
          let ast = TimbukSpec.FullParse.full_parse_to_ast fname in
          let aut = ASTBuilder.automaton ast in
          x.aut <- Some aut;
          aut
      end

    let copy (x:t)
      : t =
      create_from_timbuk (TimbukAut.copy (get_aut x))

    let add_transition
        (x:t)
        (sym:Symbol.t)
        (ss:State.t list)
        (s:State.t)
      : unit =
      TimbukAut.add_transition
        (get_aut x)
        sym
        ss
        s

    let remove_transition
        (x:t)
        (sym:Symbol.t)
        (ss:State.t list)
        (s:State.t)
      : unit =
      TimbukAut.remove_transition
        (get_aut x)
        sym
        ss
        s

    let states
        (x:t)
      : State.t list =
      TimbukAut.states (get_aut x)

    let has_state
        (x:t)
        (s:State.t)
      : bool =
      TimbukAut.has_state (get_aut x) s

    let final_states
        (x:t)
      : State.t list =
      TimbukAut.final_states (get_aut x)

    let is_final_state
        (x:t)
        (s:State.t)
      : bool =
      TimbukAut.is_final_state (get_aut x) s

    let add_final_state
        (x:t)
        (s:State.t)
      : unit =
      (TimbukAut.add_final_state (get_aut x) s)

    let remove_final_state
        (x:t)
        (s:State.t)
      : unit =
      (TimbukAut.remove_final_state (get_aut x) s)

    (*let is_empty
        (x:t)
      : bool =
      TimbukAut.is_empty (get_aut x)*)

    let transitions_from
        (x:t)
        (s:State.t)
      : (Symbol.t * State.t list * State.t) list =
      TimbukAut.transitions_from (get_aut x) s

    let transitions_to
        (x:t)
        (s:State.t)
      : (Symbol.t * State.t list) list =
      TimbukAut.transitions_to (get_aut x) s

    let transitions
        (x:t)
      : (Symbol.t * State.t list * State.t) list  =
      TimbukAut.transitions
        (get_aut x)

    let minimize
        (x:t)
      : t =
      let a = get_aut x in
      let minned =
        TimbukAut.minimize a
      in
      create_from_timbuk
        minned

    let print_of_pp x =
      fun a b -> x b a

    let to_vata_string
        a =
      let show_state s = (Id.to_string (SB.get_id s)) in
      (*let _ = A.StateSet.iter prints s1; print_endline "\n" in*)
      (*let _ = A.SymSet.iter printa alpha1; print_endline (Format.flush_str_formatter ()); print_endline "\n" in*)
      (*let aa1 = A.pp Format.std_formatter a1; print_endline "\n" in*)
      let show_symbol sy = (Id.to_string (TB.get_id sy)) in
      let show_transition
          ((t,ss,s):Symbol.t * State.t list * State.t)
        : string =
        let t_s = show_symbol t in
        let in_s =
          String.concat
            ~sep:","
            (List.map ~f:show_state ss)
        in
        let out_s = show_state s in
        t_s ^ "(" ^ in_s ^ ") -> " ^ out_s
      in
      "Ops\nAutomaton anonymous\nStates\nFinal States " ^
      (String.concat ~sep:" " (List.map ~f:show_state (final_states a))) ^
      "\nTransitions\n" ^
      (String.concat ~sep:"\n" (List.map ~f:show_transition (transitions a))) ^ "\n"

    let num = ref 0

    let next_fname
        ()
      : string =
      Core.Unix.mkdir_p "auts";
      let fname = "auts/aut" ^ (string_of_int !num) in
      incr num;
      fname


    let get_fname
        (a:t)
      : string =
      begin match a.fname with
        | None ->
          let fname = next_fname () in
          SimpleFile.write_to_file ~fname ~contents:(to_vata_string a);
          a.fname <- Some fname;
          fname
        | Some fname -> fname
      end

    let intersect
      inits
        (a1:t)
        (a2:t)
      : t =
      let fname1 = get_fname a1 in
      let fname2 = get_fname a2 in
      let new_fname = next_fname () in
      let ec_command = (!Consts.path_to_vata ^ " isect " ^ fname1 ^ " " ^ fname2 ^ " > " ^ new_fname) in
      let ec = Sys.command ec_command in
      if ec <> 0 then
        failwith (ec_command ^ " failed")
      else
        create_from_fname new_fname

    let get_small_aut
        (a:t)
      : t =
      let fname = get_fname a in
      let new_fname = next_fname () in
      let ec_command = (!Consts.path_to_vata ^ " witness " ^ fname ^ " > " ^ new_fname) in
      let ec = Sys.command ec_command in
      if ec <> 0 then
        failwith (ec_command ^ " failed")
      else
        create_from_fname new_fname

    let min_term_state
        ~(f:TermState.t -> bool)
        ~(cost:TermState.t -> Float.t)
        ~(reqs:TermState.t -> (Lang.Value.t * Lang.Value.t) list)
        (x:t)
      : term_state option =
      (*let x = get_small_aut x in*)
      let aut = get_aut x in
      let tso =
        TimbukAut.min_term_state
          ~f:(f % from_timbuk_termstate)
          ~cost:(cost % from_timbuk_termstate)
          ~reqs:(reqs % from_timbuk_termstate)
          aut
      in
      Option.map ~f:from_timbuk_termstate tso

    let size
        (x:t)
      : int =
      let x = get_aut x in
      TimbukAut.size x

    let accepting_term_state
        (x:t)
        (t:term)
      : TermState.t option =
      let x = get_aut x in
      let tso = TimbukAut.accepting_term_state x (to_timbuk_term t) in
      Option.map ~f:from_timbuk_termstate tso
  end
