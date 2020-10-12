open Collections
open Timbuk

let log_src = Logs.Src.create "timbuk.typing.simple"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type S = sig
  module Location : sig type t end
  module Aut : Automaton.S
  module OptTypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = (Aut.State.t option * Location.t)
  module Trs : Relation.S with type ord = OptTypedPattern.t
  module TypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Var.t = OptTypedPattern.Var.t and type Type.t = Aut.State.t
  module TypedTrs : Relation.S with type ord = TypedPattern.t

  type error =
    | NonLinearLHS
    | NonNormalizedTypeAut
    | Diverging of (Aut.Sym.t * Aut.State.t list)
    | InvalidType of Aut.StateSet.t option * Aut.StateSet.t option
    | UnificationFailed of Aut.StateSet.t
    | NoType
    | Ambiguity

  exception Error of error * Location.t

  type t

  val create : Trs.t -> Aut.t -> t
  val type_system : t -> Aut.t
  val typed_trs : t -> TypedTrs.t
  val type_pattern : t -> (OptTypedPattern.Var.t -> Aut.State.t option) -> OptTypedPattern.t -> (TypedPattern.t list) * t

  val print_error : error -> Format.formatter -> unit
  val error_label : error -> string option
  (* val format_error_hints : error -> CodeMap.Formatter.t -> unit *)
end

module MakeRule = Rule.Make

module Make
    (Location : sig type t end)
    (Aut : Automaton.S)
    (OptTypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = (Aut.State.t option * Location.t))
    (Trs : Relation.S with type ord = OptTypedPattern.t)
    (TypedTrs : Relation.S with type ord = (Aut.Sym.t, OptTypedPattern.Var.t, Aut.State.t) TypedPattern.typed_pattern)
= struct
  module Location = Location

  module Aut = Aut
  module OptTypedPattern = OptTypedPattern
  module Trs = Trs

  module Type = Aut.State

  module TypeSet = struct
    include Aut.StateSet

    let print t fmt =
      Format.fprintf fmt "{%t}" (Aut.StateSet.print  Type.print ", " t)
  end

  type 'a pre_result =
    | Known of 'a
    | Unknown

  module TypedPattern = TypedPattern.Make (Aut.Sym) (OptTypedPattern.Var) (Aut.State)
  (* module TypedRule = MakeRule (TypedPattern) *)
  module TypedTrs = TypedTrs

  module LHS = struct
    type t = Aut.Sym.t * Type.t list

    let compare (a, la) (b, lb) =
      let c =  Aut.Sym.compare a b in
      if c = 0 then List.compare Type.compare la lb else c

    let equal (fa, la) (fb, lb) =
      Aut.Sym.equal fa fb && List.equal Type.equal la lb

    (* let hash =
       Hashtbl.hash *)

    (* let product _ =
       None *)

    let print (f, sub_types) fmt =
      Format.fprintf fmt "%t(%t)" (Aut.Sym.print f) (List.print Type.print "," sub_types)
  end

  module LHSMap = Map.Make (LHS)

  type t = {
    trs: Trs.t;
    type_system: Aut.t;
    types: TypeSet.t;
    lhs_map: Type.t LHSMap.t;
    typed_trs: TypedTrs.t
  }

  type error =
    | NonLinearLHS
    | NonNormalizedTypeAut
    | Diverging of LHS.t
    | InvalidType of TypeSet.t option * TypeSet.t option
    | UnificationFailed of TypeSet.t
    | NoType
    | Ambiguity

  exception Error of error * Location.t

  let print_error e fmt =
    match e with
    | NonLinearLHS ->
      Format.fprintf fmt "left-hand side of functional TRS is not linear"
    | NonNormalizedTypeAut ->
      Format.fprintf fmt "type system automaton must be normalized"
    | Diverging s ->
      Format.fprintf fmt "function call `%t` diverges" (LHS.print s)
    | InvalidType _ ->
      Format.fprintf fmt "type missmatch"
    | UnificationFailed _ ->
      Format.fprintf fmt "unification failed"
    | NoType ->
      Format.fprintf fmt "no type found"
    | Ambiguity ->
      Format.fprintf fmt "ambiguity"

  let error_label e =
    match e with
    | InvalidType (Some found, Some expected) ->
      Some (Format.asprintf "expected type `%t`, found `%t`" (TypeSet.print expected) (TypeSet.print found))
    | InvalidType (None, Some expected) ->
      Some (Format.asprintf "expected type `%t`, no valid type found" (TypeSet.print expected))
    | InvalidType (Some found, None) ->
      Some (Format.asprintf "no expected types, found `%t`" (TypeSet.print found))
    | InvalidType (None, None) ->
      Some "unable to type this"
    | UnificationFailed set ->
      Some (Format.asprintf "this can be typed with %t, which are incompatible" (TypeSet.print set))
    | NoType ->
      Some "this expression has no valid type"
    | _ -> None

  (* let format_error_hints e fmt =
    match e with
    | _ -> () *)

  let create trs type_system =
    {
      trs = trs;
      type_system = type_system;
      types = Aut.states type_system;
      lhs_map = LHSMap.empty;
      typed_trs = TypedTrs.empty
    }

  let type_system t =
    t.type_system

  let typed_trs t =
    t.typed_trs

  let check_consistency a b =
    if Aut.State.equal a b then
      ()
    else begin
      Log.debug (fun m -> m "inconsistent types");
      raise (Invalid_argument "Inconsistent types.")
    end

  let merge_tys ty = function
    | Some ty' ->
      check_consistency ty ty';
      Some ty'
    | None ->
      Some ty

  let is_subtype t a b =
    Aut.recognizes_state_in b a t.type_system

  let most_precise_type2_opt t a b =
    if is_subtype t a b then
      Some a
    else if is_subtype t b a then
      Some b
    else
      None

  let least_precise_type2_opt t a b =
    if is_subtype t a b then
      Some b
    else if is_subtype t b a then
      Some a
    else
      None

  let most_precise_type2 t span a b =
    match most_precise_type2_opt t a b with
    | Some c -> c
    | None ->
      Log.debug (fun m -> m "invalid type");
      raise (Error (InvalidType (Some (TypeSet.singleton a), Some (TypeSet.singleton b)), span))

  let most_precise_type t span set =
    let unified = Aut.StateSet.fold (
        fun ty unified ->
          match TypeSet.cardinal unified with
          | 0 -> TypeSet.singleton ty
          | 1 ->
            begin match most_precise_type2_opt t ty (TypeSet.choose unified) with
              | Some ty -> TypeSet.singleton ty
              | None -> TypeSet.add ty unified
            end
          | _ ->
            let unified = TypeSet.map (
                function ty' ->
                  if is_subtype t ty' ty then
                    ty
                  else
                    ty'
              ) unified
            in
            TypeSet.add ty unified
      ) set TypeSet.empty
    in
    begin match TypeSet.cardinal unified with
      | 0 | 1 -> TypeSet.choose_opt unified
      | _ ->
        Log.debug (fun m -> m "unification failed");
        raise (Error (UnificationFailed unified, span))
    end

  let least_precise_type t span set =
    let unified = Aut.StateSet.fold (
        fun ty unified ->
          match TypeSet.cardinal unified with
          | 0 -> TypeSet.singleton ty
          | 1 ->
            begin match least_precise_type2_opt t ty (TypeSet.choose unified) with
              | Some ty -> TypeSet.singleton ty
              | None -> TypeSet.add ty unified
            end
          | _ ->
            let unified = TypeSet.map (
                function ty' ->
                  if is_subtype t ty' ty then
                    ty
                  else
                    ty'
              ) unified
            in
            TypeSet.add ty unified
      ) set TypeSet.empty
    in
    begin match TypeSet.cardinal unified with
      | 0 | 1 -> TypeSet.choose_opt unified
      | _ ->
        Log.debug (fun m -> m "unification failed");
        raise (Error (UnificationFailed unified, span))
    end

  let normalized = function
    | Aut.Configuration.Var q -> q
    | _ ->
      Log.debug (fun m -> m "non-normalized type aut");
      raise (Invalid_argument "Type-system automaton must be normalized.")

  let compare_type_opt t a b =
    if Type.equal a b then Some 0 else
    if is_subtype t a b then Some 1 else
    if is_subtype t b a then Some (-1) else
      None

  let rec compare_type_decoration_opt t (a, tya) (b, tyb) =
    match compare_type_opt t tya tyb with
    | Some 0 ->
      begin match a, b with
        | TypedPattern.Var a, TypedPattern.Var b when TypedPattern.Var.equal a b ->
          Some 0
        | TypedPattern.Cons (f, la), TypedPattern.Cons (f', lb) when TypedPattern.Sym.equal f f' ->
          let l = List.map2 (compare_type_decoration_opt t) la lb in
          if List.for_all (function Some c -> c = 0 | _ -> false) l then Some 0 else
          if List.for_all (function Some c -> c >= 0 | _ -> false) l then Some 1 else
          if List.for_all (function Some c -> c <= 0 | _ -> false) l then Some (-1) else
            None
        | _ -> None
      end
    | cmp -> cmp

  let most_precise_type_decorations t typed_patterns =
    List.fold_left (
      fun mp_typed_patterns typed_pattern ->
        let add = ref true in
        let mp_typed_patterns = List.filter (
            function typed_pattern' ->
            match compare_type_decoration_opt t typed_pattern' typed_pattern with
            | Some 0 -> false (* same types *)
            | Some 1 ->
              add := false;
              true (* more precise *)
            | Some _ -> false (* less precise *)
            | None -> true (* uncomparable *)
          ) mp_typed_patterns
        in
        if !add then typed_pattern::mp_typed_patterns else mp_typed_patterns
    ) [] typed_patterns

  let type_of (_, ty) = ty

  let span_of (_, (_, span)) = span

  let rec lhs_matching t (lhs, (_, span)) (f, l) ty =
    begin match lhs with
      | OptTypedPattern.Cons (f', l') when Aut.Sym.equal f f' ->
        begin try
            let env _ = None in
            (* Log.debug (fun m -> m "trying rule"); *)
            (* let pattern = OptTypedPattern.Cons (f, List.map2 (fun (sub, (_, span)) ty -> sub, (Some ty, span)) l' l), (Some ty, span) in *)
            let expected_sub_types = List.map (fun ty -> Some (TypeSet.singleton ty)) l in
            let typed_ls, t = type_sub_patterns t (env, false) expected_sub_types l' in
            List.fold_inline_combinations (
              fun typed_l typed_lhss ->
                let typed_lhs = TypedPattern.Cons (f, typed_l), ty in
                (* Log.debug (fun m -> m "= lhs %t" (TypedPattern.print typed_lhs)); *)
                let sigma = TypedPattern.substitution typed_lhs in
                (typed_lhs, sigma)::typed_lhss
            ) typed_ls []
          with
          | Error (_, _) -> []
        end
      | _ -> []
    end

  (** Find the type of a rule application. *)
  and apply_rule_on t span fsig =
    (* Log.debug (fun m -> m "+ apply rule on %t" (LHS.print fsig)); *)
    begin match LHSMap.find_opt fsig t.lhs_map with
      | Some ty ->
        (* Log.debug (fun m -> m "- return memorized type %t" (Type.print ty)); *)
        ty, t
      | None ->
        let apply_with ty =
          let t = { t with lhs_map = LHSMap.add fsig ty t.lhs_map } in
          let non_recursive_typing ((lhs, rhs) : Trs.elt) (t, diverges) =
            let almost_typed_lhss = lhs_matching t lhs fsig ty in
            List.fold_right (
              fun (typed_lhs, sigma) (t, _) ->
                let env x = TypedPattern.Substitution.find_opt x sigma in
                let typed_rhss, t = type_pattern t (env, true) (Some (TypeSet.singleton ty)) rhs in
                begin match most_precise_type_decorations t typed_rhss with
                  | [typed_rhs] ->
                    { t with typed_trs = TypedTrs.add (typed_lhs, typed_rhs) t.typed_trs }, false
                  | _ ->
                    (* Log.debug (fun m -> m "ambiguity"); *)
                    raise (Error (Ambiguity, span))
                end
            ) almost_typed_lhss (t, diverges)
          in
          let t, diverges = Trs.fold non_recursive_typing t.trs (t, true) in
          if diverges then begin
            (* Log.debug (fun m -> m "diverging"); *)
            raise (Error (Diverging fsig, span))
          end;
          t
        in
        let possibles_types = TypeSet.fold (
            fun ty possibles_types ->
              (* Log.debug (fun m -> m "? trying %t with %t" (LHS.print fsig) (Type.print ty)); *)
              try
                let _ = apply_with ty in
                (* Log.debug (fun m -> m "o success %t with %t" (LHS.print fsig) (Type.print ty)); *)
                TypeSet.add ty possibles_types
              with
              | _ ->
                (* Log.debug (fun m -> m "x failed %t with %t" (LHS.print fsig) (Type.print ty)); *)
                possibles_types
          ) t.types TypeSet.empty
        in
        (* Log.debug (fun m -> m "unifying possible types %t" (TypeSet.print possibles_types)); *)
        begin match most_precise_type t span possibles_types with
          | Some ty ->
            (* Log.debug (fun m -> m "found type %t" (Type.print ty)); *)
            let t = apply_with ty in
            (* Log.debug (fun m -> m "- return type %t" (Type.print ty)); *)
            ty, t
          | None ->
            (* Log.debug (fun m -> m "unification failed"); *)
            raise (Error (NoType, span))
        end
    end

  (** Try to type a pattern with multiple types. *)
  and type_pattern t (sigma, weak) (expected_tys_opt : TypeSet.t option) opt_typed_pattern : (TypedPattern.t list) * t =
    let pattern, (found_ty_opt, span) = opt_typed_pattern in
    (* begin match expected_tys_opt with
      | Some tys -> Log.debug (fun m -> m "+ type pattern %t expecting %t" (OptTypedPattern.print opt_typed_pattern) (TypeSet.print tys))
      | None -> Log.debug (fun m -> m "+ type pattern %t without expectation" (OptTypedPattern.print opt_typed_pattern))
    end; *)
    let expected_tys_opt =
      match found_ty_opt, expected_tys_opt with
      | Some found, Some expected ->
        (* if is_subtype t found expected then
           Some expected
           else
           raise (Error (InvalidType (Some found, Some expected), span)) *)
        let expected = TypeSet.filter (fun ty -> is_subtype t found ty) expected in
        if TypeSet.is_empty expected then begin
          (* Log.debug (fun m -> m "invalid expected types"); *)
          raise (Error (InvalidType (Some (TypeSet.singleton found), expected_tys_opt), span))
        end;
        Some expected
      | Some found, None -> Some (TypeSet.singleton found)
      | None, Some expected -> Some expected
      | None, None -> None
    in
    let is_expected q =
      match expected_tys_opt with
      | Some expected_tys ->
        let res = TypeSet.mem q expected_tys in
        (* if res then
           Log.debug (fun m -> m "is expected %t in %t" (Type.print q) (TypeSet.print expected_tys))
           else
           Log.debug (fun m -> m "NOT expected %t in %t" (Type.print q) (TypeSet.print expected_tys)); *)
        res
      | None ->
        (* Log.debug (fun m -> m "is expected %t" (Type.print q)); *)
        true
    in
    let refined_var_ty q =
      match expected_tys_opt, weak with
      | Some expected_tys, true ->
        let refined_tys = TypeSet.filter (is_subtype t q) expected_tys in
        if TypeSet.is_empty refined_tys then begin
          (* Log.debug (fun m -> m "invalid refined types"); *)
          raise (Error (InvalidType (Some (TypeSet.singleton q), expected_tys_opt), span))
        end;
        refined_tys
      | _, false ->
        if is_expected q then TypeSet.singleton q else begin
          (* Log.debug (fun m -> m "invalid expected types"); *)
          raise (Error (InvalidType (Some (TypeSet.singleton q), expected_tys_opt), span))
        end
      | _ -> TypeSet.singleton q
    in
    (* begin match expected_tys_opt with
       | Some tys -> Log.debug (fun m -> m "typing %t with %t" (OptTypedPattern.print (pattern, (found_ty_opt, span))) (TypeSet.print tys))
       | None -> Log.debug (fun m -> m "typing %t" (OptTypedPattern.print (pattern, (found_ty_opt, span))))
       end; *)
    begin match pattern with
      | OptTypedPattern.Var x ->
        let tys = match sigma x with
          | Some ty ->
            (* Log.debug (fun m -> m "var type is %t" (Type.print ty)); *)
            refined_var_ty ty
          | None ->
            begin match expected_tys_opt with
              | Some tys -> tys
              | None ->
                (* Log.debug (fun m -> m "untyped variable"); *)
                raise (Error (InvalidType (None, None), span))
            end
        in
        let typed_patterns = TypeSet.fold (
            fun ty typed_patterns ->
              let typed_pattern = TypedPattern.Var x, ty in
              (* Log.debug (fun m -> m "= typed %t" (TypedPattern.print typed_pattern)); *)
              typed_pattern::typed_patterns
          ) tys []
        in
        if typed_patterns = [] then begin
          (* Log.debug (fun m -> m "no type found"); *)
          raise (Error (NoType, span))
        end;
        (* Log.debug (fun m -> m "- found [ %t ]" (List.print TypedPattern.print "; " typed_patterns)); *)
        typed_patterns, t
      | OptTypedPattern.Cons (f, l) ->
        let arity = List.length l in
        (* Find the possibles types for each sub pattern. *)
        let empty_sub_tys = List.init arity (fun _ -> Aut.StateSet.empty) in
        let expected_sub_tys = Aut.fold_transitions (
            fun conf _ ty expected_sub_tys ->
              match conf with
              | Aut.Configuration.Cons (f', l') when Aut.Sym.equal f f' && is_expected ty ->
                List.map2 (
                  fun sub_conf tys ->
                    match sub_conf with
                    | Aut.Configuration.Var q -> Aut.StateSet.add q tys
                    | _ ->
                      (* Log.debug (fun m -> m "non normalized automaton"); *)
                      raise (Error (NonNormalizedTypeAut, span))
                ) l' expected_sub_tys
              | _ -> expected_sub_tys
          ) t.type_system empty_sub_tys
        in
        (* If no type has been found. *)
        let typed_patterns, t = if List.exists TypeSet.is_empty expected_sub_tys then begin
            (* A rule must apply. *)
            (* Type every sub pattern with no expectations. *)
            let expected_sub_tys = List.init arity (fun _ -> None) in
            let typed_ls, t = type_sub_patterns t (sigma, weak) expected_sub_tys l in
            (* Follow the rule. *)
            List.fold_inline_combinations (
              fun typed_l (typed_patterns, t) ->
                (* Extract the found sub types. *)
                let sub_types = List.map type_of typed_l in
                let ty, t = apply_rule_on t span (f, sub_types) in
                if is_expected ty then
                  let typed_pattern = TypedPattern.Cons (f, typed_l), ty in
                  (* Log.debug (fun m -> m "= typed %t" (TypedPattern.print typed_pattern)); *)
                  (typed_pattern::typed_patterns, t)
                else
                  (typed_patterns, t)
            ) typed_ls ([], t)
          end else begin (* If types has been found. *)
            (* Type every sub pattern with the expected sub types. *)
            let expected_sub_tys = List.map (fun ty -> Some ty) expected_sub_tys in
            let typed_ls, t = type_sub_patterns t (sigma, weak) expected_sub_tys l in
            List.fold_inline_combinations (
              fun typed_l (typed_patterns, t) ->
                (* Extract the found sub types. *)
                let sub_types = List.map type_of typed_l in
                (* Find every possible type given the sub types. *)
                (* This also allows us to refine the possible sub types. *)
                let typed_conf = Aut.Configuration.Cons (f, List.map Aut.Configuration.of_var sub_types) in
                let tys = Aut.states_for_configuration typed_conf t.type_system in
                let tys = Aut.LabeledStateSet.fold (fun (q, _) set -> TypeSet.add q set) tys TypeSet.empty in
                let typed_patterns = TypeSet.fold (
                    fun ty typed_patterns ->
                      if is_expected ty then
                        let typed_pattern = TypedPattern.Cons (f, typed_l), ty in
                        (* Log.debug (fun m -> m "= typed %t" (TypedPattern.print typed_pattern)); *)
                        typed_pattern::typed_patterns
                      else
                        typed_patterns
                  ) tys typed_patterns
                in
                (typed_patterns, t)
            ) typed_ls ([], t)
          end
        in
        if typed_patterns = [] then begin
          (* Log.debug (fun m -> m "no type found"); *)
          (* begin match expected_tys_opt with
             | Some tys -> Log.debug (fun m -> m "! not type for %t with %t" (OptTypedPattern.print (pattern, (found_ty_opt, span))) (TypeSet.print tys))
             | None -> Log.debug (fun m -> m "! not type for %t" (OptTypedPattern.print (pattern, (found_ty_opt, span))))
             end; *)
          raise (Error (NoType, span))
        end;
        (* Log.debug (fun m -> m "- found [ %t ]" (List.print TypedPattern.print "; " typed_patterns)); *)
        typed_patterns, t
      | OptTypedPattern.Cast _ ->
        (* Log.debug (fun m -> m "casts not handled"); *)
        raise (Invalid_argument "casts are not handled by the typing algorithm")
    end

  and type_sub_patterns t (sigma, weak) (expected_sub_tys : TypeSet.t option list) patterns : (TypedPattern.t list) list * t =
    let typed_patterns, t = List.fold_right2 (
        fun pattern expected_tys (typed_patterns, t) ->
          let typed_sub_patterns, t = type_pattern t (sigma, weak) expected_tys pattern in
          typed_sub_patterns::typed_patterns, t
      ) patterns expected_sub_tys ([], t)
    in
    typed_patterns, t

  (** Type a pattern with a unique type. *)
  let type_pattern t (sigma : OptTypedPattern.Var.t -> Type.t option) pattern =
    let typed_patterns, t = type_pattern t (sigma, false) None pattern in
    most_precise_type_decorations t typed_patterns, t
end
