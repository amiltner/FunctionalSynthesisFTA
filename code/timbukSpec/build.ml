open Timbuk
open TimbukTyping
open Spec
open CodeMap

type item_kind =
  | Atom (* symbol, variable or state *)
  | Trs
  | Automaton
  | PatternSet

type error =
  | ProtectedSymbol of string
  | AlreadyDefined of string * item_kind * Span.t
  | UndefinedSymbolOrVar of string
  | UndefinedSymbolOrState of string
  | UndefinedState of string
  | UndefinedAutomaton of string
  | VariableSubterms of string * Span.t (* give the variable definition site. *)
  | StateSubterms of string * Span.t (* give the variable definition site. *)
  | InvalidArity of int * int * Span.t (* give the found arity, the expected arity, and the symbol def site. *)
  | NotAState of Span.t
  | NoTypeSystem of string * Span.t (* give the pattern set definition site. *)

let print_error e fmt =
  match e with
  | ProtectedSymbol id ->
    Format.fprintf fmt "the symbol `%s` is protected and cannot be redefined" id
  | AlreadyDefined (id, Atom, _) ->
    Format.fprintf fmt "`%s` is already defined" id
  | AlreadyDefined (id, Trs, _) ->
    Format.fprintf fmt "rewriting system `%s` is already defined" id
  | AlreadyDefined (id, Automaton, _) ->
    Format.fprintf fmt "automaton `%s` is already defined" id
  | AlreadyDefined (id, PatternSet, _) ->
    Format.fprintf fmt "pattern set `%s` is already defined" id
  | UndefinedSymbolOrVar id ->
    Format.fprintf fmt "undefined symbol or variable `%s`" id
  | UndefinedSymbolOrState id ->
    Format.fprintf fmt "undefined symbol or state `%s`" id
  | UndefinedState id ->
    Format.fprintf fmt "undefined state `%s`" id
  | UndefinedAutomaton id ->
    Format.fprintf fmt "undefined automaton `%s`" id
  | VariableSubterms (id, _) ->
    Format.fprintf fmt "`%s` is a variable and cannot have subterms" id
  | StateSubterms (id, _) ->
    Format.fprintf fmt "`%s` is a state and cannot have subterms" id
  | InvalidArity (found, expected, _) ->
    Format.fprintf fmt "wrong arity (expected %d, found %d)" expected found
  | NotAState _ ->
    Format.fprintf fmt "invalid automaton configuration"
  | NoTypeSystem _ ->
    Format.fprintf fmt "no type system specified"

let error_label e =
  match e with
  | ProtectedSymbol _ ->
    Some "used to define higher-order rewriting systems and terms"
  | InvalidArity (0, _, _) ->
    Some "...but occurs here with no subterms"
  | InvalidArity (1, 0, _) ->
    Some "...but occurs here with a subterm"
  | InvalidArity (1, _, _) ->
    Some "...but occurs here with only one subterm"
  | InvalidArity (arity, _, _) ->
    Some (Format.asprintf "...but occurs here with %d subterms" arity)
  | NoTypeSystem _ ->
    Some "where does this state come from?"
  | _ -> None

let format_error_hints e fmt =
  match e with
  | AlreadyDefined (_, _, def_site) ->
    Formatter.add fmt def_site (Some "first definition here") Formatter.Highlight.Note;
  | VariableSubterms (_, def_site) ->
    Formatter.add fmt def_site (Some "variable defined here") Formatter.Highlight.Note;
  | StateSubterms (_, def_site) ->
    Formatter.add fmt def_site (Some "state defined here") Formatter.Highlight.Note;
  | InvalidArity (_, arity, def_site) ->
    let label = Format.asprintf "symbol defined here with arity %d..." arity in
    Formatter.add fmt def_site (Some label) Formatter.Highlight.Note;
  | NotAState rhs_span ->
    Formatter.add fmt rhs_span (Some "this should be a state") Formatter.Highlight.Note;
  | NoTypeSystem (trs_id, set_def) ->
    let label = Format.asprintf "you can specify an automaton as type system by writing `%s : A` here" trs_id in
    Formatter.add fmt set_def (Some label) Formatter.Highlight.Note;
  | _ -> ()

exception Error of error * Span.t

let alphabet (ast, _) =
  List.fold_left (
    fun alphabet (sym, span) ->
      let id = fst sym.Ast.sym_name in
      if id = "@" then raise (Error (ProtectedSymbol "@", span));
      let arity = fst sym.Ast.sym_arity in
      let sym = AppSymbol.Sym (StringSymbol.create id arity) in
      try Alphabet.add id (sym, span) alphabet with
      | Alphabet.AlreadyDefined span' -> raise (Error (AlreadyDefined (id, Atom, span'), span))
  ) Alphabet.empty ast

let variables alphabet (ast, _) =
  List.fold_left (
    fun vars (x, span) ->
      let id = fst x.Ast.var_name in
      if id = "@" then raise (Error (ProtectedSymbol "@", span));
      let x = Var.create () in
      match Alphabet.find_opt id alphabet with
      | Some (_, span') -> raise (Error (AlreadyDefined (id, Atom, span'), span))
      | None ->
        begin try Variables.add id (x, span) vars with
          | Variables.AlreadyDefined span' -> raise (Error (AlreadyDefined (id, Atom, span'), span))
        end
  ) Variables.empty ast

module States = Dictionary.Make (Id) (State)

let states alphabet (ast, _) =
  List.fold_left (
    fun states (q, span) ->
      let id = fst q.Ast.state_name in
      if id = "@" then raise (Error (ProtectedSymbol "@", span));
      let q = GenericTypes.PolyBase (UserState.of_string id) in
      match Alphabet.find_opt id alphabet with
      | Some (_, span') -> raise (Error (AlreadyDefined (id, Atom, span'), span))
      | None ->
        begin try States.add id (q, span) states with
          | States.AlreadyDefined span' -> raise (Error (AlreadyDefined (id, Atom, span'), span))
        end
  ) States.empty ast

let final_states states (ast, _) =
  List.fold_left (
    fun roots (q, span) ->
      let id = fst q.Ast.state_name in
      match States.find_opt id states with
      | Some (q, _) -> Aut.StateSet.add q roots
      | None ->
        raise (Error (UndefinedState id, span))
  ) Aut.StateSet.empty ast

let rec pattern alphabet variables states (ast, span) =
  let id, id_span = ast.Ast.term_cons in
  let ty = match ast.Ast.term_type with
    | Some (qid, qid_span) ->
      begin match states with
        | Some states ->
          let q = GenericTypes.PolyBase (UserState.of_string qid) in
          if not (Aut.StateSet.mem q states) then
            raise (Error (UndefinedState qid, qid_span));
          Some q
        | None -> raise (Error (NoTypeSystem ("", qid_span), qid_span))
      end
    | None -> None
  in
  if id = "@" then
    let subs = List.map (pattern alphabet variables states) (fst ast.Ast.term_subs) in
    LocPattern.Cons (AppSymbol.App, subs), (ty, span)
  else
    match Alphabet.find_opt id alphabet with
    | Some (f, f_def_span) ->
      let arity = List.length (fst ast.Ast.term_subs) in
      if arity <> Symbol.arity f then raise (Error (InvalidArity (arity, Symbol.arity f, f_def_span), span));
      let subs = List.map (pattern alphabet variables states) (fst ast.Ast.term_subs) in
      LocPattern.Cons (f, subs), (ty, span)
    | None ->
      match Variables.find_opt id variables with
      | Some (x, x_def_span) ->
        if fst ast.Ast.term_subs <> [] then raise (Error (VariableSubterms (id, x_def_span), span));
        LocPattern.Var x, (ty, span)
      | None ->
        raise (Error (UndefinedSymbolOrVar id, id_span))

let rules alphabet variables (ast, _) =
  List.fold_left (
    fun rules (rule, span) ->
      let lhs = pattern alphabet variables None rule.Ast.rule_left in
      let rhs = pattern alphabet variables None rule.Ast.rule_right in
      (lhs, rhs)::rules
  ) [] ast

let trs alphabet variables (ast, _) =
  let (id, _) = ast.Ast.trs_name in
  let rules = rules alphabet variables ast.Ast.trs_rules in
  let trs = List.fold_right LocTrs.add rules LocTrs.empty in
  id, trs

let trss alphabet variables ast =
  List.fold_left (
    fun trss (ast, span) ->
      let id, trs = trs alphabet variables (ast, span) in
      try Trss.add id (trs, span) trss with
      | Trss.AlreadyDefined span' -> raise (Error (AlreadyDefined (id, Trs, span'), span))
  ) Trss.empty ast

let rec configuration alphabet states (ast, span) =
  let id, id_span = ast.Ast.term_cons in
  if id = "@" then
    let subs = List.map (configuration alphabet states) (fst ast.Ast.term_subs) in
    Aut.Configuration.Cons (AppSymbol.App, subs)
  else
    match Alphabet.find_opt id alphabet with
    | Some (f, f_def_span) ->
      let arity = List.length (fst ast.Ast.term_subs) in
      if arity <> Symbol.arity f then raise (Error (InvalidArity (arity, Symbol.arity f, f_def_span), span));
      let subs = List.map (configuration alphabet states) (fst ast.Ast.term_subs) in
      Aut.Configuration.Cons (f, subs)
    | None ->
      match States.find_opt id states with
      | Some (q, q_def_span) ->
        if fst ast.Ast.term_subs <> [] then raise (Error (StateSubterms (id, q_def_span), span));
        Aut.Configuration.Var q
      | None ->
        raise (Error (UndefinedSymbolOrState id, id_span))

let transitions alphabet states (ast, span) =
  List.fold_left (
    fun rules (rule, span) ->
      let lhs = configuration alphabet states rule.Ast.rule_left in
      let q = match configuration alphabet states rule.Ast.rule_right with
        | Aut.Configuration.Cons _ -> raise (Error (NotAState (snd rule.Ast.rule_right), span))
        | Aut.Configuration.Var q -> q
      in
      (lhs, q)::rules
  ) [] ast

let automaton alphabet (ast, _) =
  let (id, _) = ast.Ast.aut_name in
  let states = states alphabet ast.Ast.aut_states in
  let roots = final_states states ast.Ast.aut_roots in
  let transitions = transitions alphabet states ast.Ast.aut_transitions in
  let aut = List.fold_left (fun aut (conf, q) -> Aut.add_transition conf () q aut) (Aut.create ()) transitions in
  let aut = Aut.add_final_states roots aut in
  id, aut

let automata alphabet ast =
  List.fold_left (
    fun automata (ast, span) ->
      let id, aut = automaton alphabet (ast, span) in
      try Automata.add id (aut, span) automata with
      | Automata.AlreadyDefined span' -> raise (Error (AlreadyDefined (id, Automaton, span'), span))
  ) Automata.empty ast

let pattern_set alphabet variables automata (ast, _) =
  let (id, id_span) = ast.Ast.pset_name in
  let type_system, states = match ast.Ast.pset_type_system with
    | Some (ts_id, span) ->
      begin match Automata.find_opt ts_id automata with
        | Some (ts, _) ->
          Some ts, Some (Aut.states ts)
        | None -> raise (Error (UndefinedAutomaton ts_id, span))
      end
    | None -> None, None
  in
  try
    let set = List.fold_left (
        fun set (ast, span) ->
          let source_pattern : LocPattern.t = pattern alphabet variables states ast.Ast.src_pattern in
          let target_type = match ast.Ast.src_target_type with
            | Some (target_ty, target_ty_span) ->
              begin match states with
                | Some states ->
                  let q = GenericTypes.PolyBase (UserState.of_string target_ty) in
                  if not (Aut.StateSet.mem q states) then
                    raise (Error (UndefinedState target_ty, target_ty_span));
                  Some (Aut.StateSet.singleton q)
                | None -> raise (Error (NoTypeSystem ("", target_ty_span), target_ty_span))
              end
            | None -> None
          in
          LocPatternSet.add (source_pattern, target_type) set
      ) LocPatternSet.empty (fst ast.Ast.pset_patterns)
    in
    id, (set, type_system)
  with
  | Error (NoTypeSystem (_, _), span) -> raise (Error (NoTypeSystem (id, id_span), span))

let pattern_sets alphabet variables automata ast =
  List.fold_left (
    fun pattern_sets (ast, span) ->
      let id, set = pattern_set alphabet variables automata (ast, span) in
      try PatternSets.add id (set, span) pattern_sets with
      | PatternSets.AlreadyDefined span' -> raise (Error (AlreadyDefined (id, PatternSet, span'), span))
  ) PatternSets.empty ast

let specification (ast, _) =
  let alphabet = alphabet ast.Ast.spec_alphabet in
  let vars = variables alphabet ast.Ast.spec_variables in
  let automata = automata alphabet ast.Ast.spec_automata in
  let trss = trss alphabet vars ast.Ast.spec_trss in
  let pattern_sets = pattern_sets alphabet vars automata ast.Ast.spec_pattern_sets in
  {
    spec_alphabet = alphabet;
    spec_variables = vars;
    spec_trss = trss;
    spec_automata = automata;
    spec_pattern_sets = pattern_sets
  }
