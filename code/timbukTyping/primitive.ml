open Collections
open Timbuk

let log_src = Logs.Src.create "timbuk.typing.primitive"
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
    | NoRuleMatch of (Aut.Sym.t * Aut.State.t list)
    | InvalidType of Aut.State.t option * Aut.State.t option
    | UnificationFailed of Aut.State.t * Aut.State.t
    | NoType

  exception Error of error * Location.t

  type t

  type ho_helper = {
    is_application: Aut.Sym.t -> bool;
    make_application: int -> bool
  }

  val create : ?ho:ho_helper -> Trs.t -> Aut.t -> t
  val type_system : t -> Aut.t
  val typed_trs : t -> TypedTrs.t
  val type_pattern : t -> (OptTypedPattern.Var.t -> Aut.State.t option) -> OptTypedPattern.t -> TypedPattern.t * t

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

  type ho_helper = {
    is_application: Aut.Sym.t -> bool;
    make_application: int -> bool
  }

  type t = {
    ho: ho_helper option;
    trs: Trs.t;
    type_system: Aut.t;
    lhs_map: (Type.t pre_result) LHSMap.t;
    typed_trs: TypedTrs.t
  }

  type error =
    | NonLinearLHS
    | NonNormalizedTypeAut
    | Diverging of LHS.t
    | NoRuleMatch of LHS.t
    | InvalidType of Type.t option * Type.t option
    | UnificationFailed of Type.t * Type.t
    | NoType

  exception Error of error * Location.t

  let print_error e fmt =
    match e with
    | NonLinearLHS ->
      Format.fprintf fmt "left-hand side of functional TRS is not linear"
    | NonNormalizedTypeAut ->
      Format.fprintf fmt "type system automaton must be normalized"
    | Diverging s ->
      Format.fprintf fmt "function call `%t` diverges" (LHS.print s)
    | NoRuleMatch s ->
      Format.fprintf fmt "no rule matches function call `%t`" (LHS.print s)
    | InvalidType _ ->
      Format.fprintf fmt "type missmatch"
    | UnificationFailed _ ->
      Format.fprintf fmt "unification failed"
    | NoType ->
      Format.fprintf fmt "no type found"

  let error_label e =
    match e with
    | NoRuleMatch _ ->
      Some "unable to rewrite this"
    | InvalidType (Some found, Some expected) ->
      Some (Format.asprintf "expected type `%t`, found `%t`" (Type.print expected) (Type.print found))
    | InvalidType (None, Some expected) ->
      Some (Format.asprintf "expected type `%t`, no valid type found" (Type.print expected))
    | InvalidType (Some found, None) ->
      Some (Format.asprintf "no expected types, found `%t`" (Type.print found))
    | InvalidType (None, None) ->
      Some "unable to type this"
    | UnificationFailed (a, b) ->
      Some (Format.asprintf "this can be typed with `%t` and `%t`, which are incompatible" (Aut.State.print a) (Aut.State.print b))
    | NoType ->
      Some "this expression has no valid type"
    | _ -> None

  (* let format_error_hints e fmt =
    match e with
    | _ -> () *)

  let create ?ho trs type_system =
    {
      ho = ho;
      trs = trs;
      type_system = type_system;
      lhs_map = LHSMap.empty;
      typed_trs = TypedTrs.empty
    }

  let is_application t f =
    match t.ho with
    | Some ho -> ho.is_application f
    | None -> false

  let make_application t i f =
    match t.ho with
    | Some ho -> ho.make_application i
    | None -> failwith "no ho helper"

  let type_system t =
    t.type_system

  let typed_trs t =
    t.typed_trs

  let check_consistency a b =
    if Aut.State.equal a b then
      ()
    else
      raise (Invalid_argument "Inconsistent types.")

  let merge_tys ty = function
    | Some ty' ->
      check_consistency ty ty';
      Some ty'
    | None ->
      Some ty

  let is_subtype t a b =
    Aut.recognizes_state_in b a t.type_system

  let unify2_opt t a b =
    if is_subtype t a b then
      Some a
    else if is_subtype t b a then
      Some b
    else
      None

  let unify2 t span a b =
    match unify2_opt t a b with
    | Some c -> c
    | None -> raise (Error (InvalidType (Some a, Some b), span))

  let unify t span set =
    Aut.StateSet.fold (
      fun ty unified ->
        match unified with
        | Some ty' ->
          begin match unify2_opt t ty ty' with
            | Some ty -> Some ty
            | None -> raise (Error (UnificationFailed (ty, ty'), span))
          end
        | None -> Some ty
    ) set None

  let normalized = function
    | Aut.Configuration.Var q -> q
    | _ ->
      raise (Invalid_argument "Type-system automaton must be normalized.")

  let type_of (_, ty) = ty

  let span_of (_, (_, span)) = span

  exception Recursive of (Aut.Sym.t * Aut.State.t list) * t

  let rec lhs_matching t (lhs, (_, span)) (f, l) =
    let linear _ _ = raise (Error (NonLinearLHS, span)) in
    begin match lhs with
      | OptTypedPattern.Cons (f', l') when Aut.Sym.equal f f' ->
        begin try
            let env _ = None in
            let typed_l = List.map2 (fun pattern tys -> fst (type_pattern t env (Some tys) pattern)) l' l in
            let sigma = List.fold_right (
                fun typed_pattern sigma ->
                  let sigma' = TypedPattern.substitution typed_pattern in
                  TypedPattern.Substitution.union linear sigma sigma'
              ) typed_l TypedPattern.Substitution.empty
            in
            Some (TypedPattern.Cons (f, typed_l), sigma)
          with
          | Error (_, _) -> None
        end
      | _ -> None
    end

  (** Find the type of a rule application. *)
  and apply_rule_on t span fsig =
    let f, sub_tys = fsig in
    (* Log.debug (fun m -> m "typing rules matching %t" (LHS.print (f, sub_tys))); *)
    let exception Found of (Type.t * t) in
    let _ = 0 in (* For the syntax coloring in Atom... :( *)
    (* First we see if we haven't already found the type for this application. *)
    begin match LHSMap.find_opt fsig t.lhs_map with
      | Some Unknown ->
        raise (Recursive (fsig, t))
      | Some (Known ty) -> ty, t
      | None ->
        (* Log.debug (fun m -> m "unknown"); *)
        let t = { t with lhs_map = LHSMap.add fsig Unknown t.lhs_map } in
        (* First we try without knowing anything. *)
        begin try
            let matches_some_rule = ref false in
            let non_recursive_typing ((lhs, rhs) : Trs.elt) t =
              match lhs_matching t lhs (f, sub_tys) with
              | Some (almost_typed_lhs, sigma) ->
                begin try
                    matches_some_rule := true;
                    let sigmaf x = TypedPattern.Substitution.find_opt x sigma in
                    let typed_rhs, t = type_pattern t sigmaf None rhs in
                    (* Log.debug (fun m -> m "found %t" (TypedPattern.print typed_rhs)); *)
                    raise (Found (type_of typed_rhs, t))
                  with
                  | Recursive (fsig', t) ->
                    (* Log.debug (fun m -> m "CATCH recursive case %t in %t" (LHS.print fsig') (LHS.print fsig)); *)
                    let t = { t with lhs_map = LHSMap.remove fsig t.lhs_map } in
                    if LHS.equal fsig fsig' then t else
                      raise (Recursive (fsig', t))
                end
              | None -> t
            in
            let _ = Trs.fold non_recursive_typing t.trs t in
            if !matches_some_rule then
              raise (Error (Diverging (f, sub_tys), span))
            else
              raise (Error (NoRuleMatch (f, sub_tys), span))
          with
          | Found (ty, t) ->
            let t = { t with lhs_map = LHSMap.add fsig (Known ty) t.lhs_map } in
            (* Log.debug (fun m -> m "known %t:%t" (LHS.print fsig) (Type.print ty)); *)
            (* Then we retry with knowledge. *)
            let recursive_typing (lhs, rhs) (ty, t) =
              match lhs_matching t lhs (f, sub_tys) with
              | Some (almost_typed_lhs, sigma) ->
                let sigmaf x = TypedPattern.Substitution.find_opt x sigma in
                let typed_rhs, t = type_pattern t sigmaf (Some ty) rhs in
                let typed_lhs = almost_typed_lhs, ty in
                (* let ty = type_of typed_rhs in *)
                (* let t = { t with lhs_map = LHSMap.add fsig (Known ty) t.lhs_map } in *)
                (* (almost_typed_lhs, typed_rhs, sigma)::trs, tys, t *)
                ty, { t with typed_trs = TypedTrs.add (typed_lhs, typed_rhs) t.typed_trs }
              | None -> ty, t
            in
            let ty, t = Trs.fold recursive_typing t.trs (ty, t) in
            ty, t
        end
    end

  (** Try to type a pattern with multiple types. *)
  and type_pattern t (sigma : OptTypedPattern.Var.t -> Type.t option) expected_ty_opt (pattern, (found_ty_opt, span)) : TypedPattern.t * t =
    let ty_opt_enforce found expected =
      match found, expected with
      | Some found, Some expected ->
        if is_subtype t found expected then
          Some expected
        else
          raise (Error (InvalidType (Some found, Some expected), span))
      | Some found, None -> Some found
      | None, Some expected -> Some expected
      | None, None -> None
    in
    let is_expected q =
      match expected_ty_opt with
      | Some expected_ty -> Aut.State.equal q expected_ty
      | None -> true
    in
    (* begin match expected_tys_opt with
       | Some tys -> Log.debug (fun m -> m "typing %t with %t" (OptTypedPattern.print (pattern, (found_ty_opt, span))) (TypeSet.print tys))
       | None -> Log.debug (fun m -> m "typing %t" (OptTypedPattern.print (pattern, (found_ty_opt, span))))
       end; *)
    begin match pattern with
      | OptTypedPattern.Var x ->
        let found_ty_opt = sigma x in
        begin match ty_opt_enforce found_ty_opt expected_ty_opt with
          | Some ty ->
            let typed_pattern = TypedPattern.Var x, ty in
            typed_pattern, t
          | None -> raise (Error (InvalidType (found_ty_opt, expected_ty_opt), span))
        end
      | OptTypedPattern.Cons (f, l) ->
        let arity = List.length l in
        (* Find the possibles types for each sub pattern. *)
        let empty_sub_tys = List.init arity (fun _ -> Aut.StateSet.empty) in
        let expected_sub_tys = Aut.fold_transitions (
            fun conf _ q expected_sub_tys ->
              match conf with
              | Aut.Configuration.Cons (f', l') when Aut.Sym.equal f f' && is_expected q ->
                List.map2 (
                  fun sub_conf tys ->
                    match sub_conf with
                    | Aut.Configuration.Var q -> Aut.StateSet.add q tys
                    | _ -> raise (Error (NonNormalizedTypeAut, span))
                ) l' expected_sub_tys
              | _ -> expected_sub_tys
          ) t.type_system empty_sub_tys
        in
        let expected_sub_tys = List.map2 (fun tys p -> unify t (span_of p) tys) expected_sub_tys l in
        (* If no type has been found. *)
        if List.exists Option.is_none expected_sub_tys then begin
          (* A rule must apply. *)
          (* Type every sub pattern with no expectations. *)
          let expected_sub_tys = List.init arity (fun _ -> None) in
          let typed_l, t = type_sub_patterns t sigma l expected_sub_tys in
          (* Extract the found sub types. *)
          let sub_types = List.map type_of typed_l in
          (* Follow the rule. *)
          let ty, t = apply_rule_on t span (f, sub_types) in
          let typed_pattern: TypedPattern.t = TypedPattern.Cons (f, typed_l), ty in
          (* Log.debug (fun m -> m "prim typed %t" (TypedPattern.print typed_pattern)); *)
          typed_pattern, t
        end else begin (* If types has been found. *)
          (* Type every sub pattern with the expected sub types. *)
          let typed_l, t = type_sub_patterns t sigma l expected_sub_tys in
          (* Extract the found sub types. *)
          let sub_types = List.map type_of typed_l in

          (* Find every possible type given the sub types. *)
          (* This also allows us to refine the possible sub types. *)
          let typed_conf = Aut.Configuration.Cons (f, List.map Aut.Configuration.of_var sub_types) in
          let tys = Aut.states_for_configuration typed_conf t.type_system in
          let tys = Aut.LabeledStateSet.fold (fun (q, _) set -> Aut.StateSet.add q set) tys Aut.StateSet.empty in
          let ty = match unify t span tys with
            | Some ty ->
              Option.get (ty_opt_enforce (Some ty) expected_ty_opt)
            | None -> raise (Error (NoType, span))
          in
          let typed_pattern = TypedPattern.Cons (f, typed_l), ty in
          (* Log.debug (fun m -> m "prim typed %t" (TypedPattern.print typed_pattern)); *)
          typed_pattern, t
        end
      | OptTypedPattern.Cast _ -> raise (Invalid_argument "casts are not handled by the typing algorithm")
    end

  and type_sub_patterns t (sigma : OptTypedPattern.Var.t -> Type.t option) patterns expected_sub_tys : TypedPattern.t list * t =
    let typed_patterns, t = List.fold_right2 (
        fun pattern expected_tys (typed_patterns, t) ->
          let typed_pattern, t = type_pattern t sigma expected_tys pattern in
          typed_pattern::typed_patterns, t
      ) patterns expected_sub_tys ([], t)
    in
    typed_patterns, t

  (** Type a pattern with a unique type. *)
  let type_pattern t (sigma : OptTypedPattern.Var.t -> Type.t option) pattern =
    type_pattern t sigma None pattern
end
