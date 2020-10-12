open Collections
open Timbuk

let log_src = Logs.Src.create "timbuk.typing.sub"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type S = sig
  module Location : sig type t end
  module Aut : Automaton.S
  module TypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = Aut.State.t * Location.t
  module TypedTrs : Relation.S with type ord = TypedPattern.t

  type error =
    | Ambiguity
    | UnificationFailed of Aut.StateSet.t

  exception Error of error * Location.t

  type t

  val create : Aut.t -> TypedTrs.t -> t
  val type_system : t -> Aut.t
  val typed_trs : t -> TypedTrs.t
  val type_pattern : TypedPattern.t -> t -> TypedPattern.t list * t

  val print_error : error -> Format.formatter -> unit
  val error_label : error -> string option
  (* val format_error_hints : error -> CodeMap.Formatter.t -> unit *)
end

module Make
    (Location : sig type t end)
    (Aut : Automaton.S)
    (TypedPattern : TypedPattern.S with type Sym.t = Aut.Sym.t and type Type.t = Aut.State.t * Location.t)
    (TypedTrs : Relation.S with type ord = TypedPattern.t)
= struct
  module Location = Location
  module Aut = Aut
  module TypedPattern = TypedPattern
  module TypedTrs = TypedTrs

  module Type = Aut.State

  module TypeSet = struct
    include Aut.StateSet

    let print t fmt =
      Format.fprintf fmt "{%t}" (Aut.StateSet.print  Type.print ", " t)
  end

  module SymSig = struct
    type t = Aut.Sym.t * Type.t list * Type.t

    let compare (fa, la, ta) (fb, lb, tb) =
      let c = Aut.Sym.compare fa fb in
      if c = 0 then
        let c =  Type.compare ta tb in
        if c = 0 then List.compare Type.compare la lb else c
      else c

    let equal (fa, la, ta) (fb, lb, tb) =
      Aut.Sym.equal fa fb && Type.equal ta tb && List.equal Type.equal la lb

    let hash = Hashtbl.hash

    (* let product _ =
       None *)

    let print (f, sub_types, ty) fmt =
      Format.fprintf fmt "%t(%t):%t" (Aut.Sym.print f) (List.print Type.print "," sub_types) (Type.print ty)
  end

  module SymSigTable = HashTable.Make (SymSig)

  type t = {
    trs: TypedTrs.t;
    type_system: Aut.t;
    typed_trs: TypedTrs.t;

    sig_table: bool SymSigTable.t;
  }

  type error =
    | Ambiguity
    | UnificationFailed of Aut.StateSet.t

  exception Error of error * Location.t

  let print_error e fmt =
    match e with
    | UnificationFailed _ ->
      Format.fprintf fmt "unification failed"
    | Ambiguity ->
      Format.fprintf fmt "ambiguity"

  let error_label e =
    match e with
    | UnificationFailed set ->
      Some (Format.asprintf "this can be typed with %t, which are incompatible" (TypeSet.print set))
    | _ -> None

  (* let format_error_hints e fmt =
    match e with
    | _ -> () *)

  let span_of (_, (_, span)) = span

  let type_of (_, (ty, _)) = ty

  let with_ty ty pattern = Type.equal ty (type_of pattern)

  (* [type_family t ty] returns the set containing [ty] and all its sub types. *)
  let rec type_family t ty : Aut.StateSet.t =
    let confs = Aut.configurations_for_state ty t.type_system in
    Aut.LabeledConfigurationSet.fold (
      fun (conf, _) family ->
        match conf with
        | Aut.Configuration.Var sub_ty ->
          TypeSet.union (type_family t sub_ty) family
        | _ -> family
    ) confs (TypeSet.singleton ty)

  (* [type_family_cast t super_ty ty] returns th set containing [ty], all its
     sub types, and also all the intermediate types between [ty] and its parent
     type [super_ty]. *)
  let rec type_family_cast t super_ty ty =
    if Type.equal super_ty ty then
      type_family t ty
    else
      let sub_types = Aut.sub_states_of t.type_system super_ty in
      let family = Aut.StateSet.fold (
          fun sub_ty family ->
            let sub_family = type_family_cast t sub_ty ty in
            TypeSet.union sub_family family
        ) sub_types TypeSet.empty
      in
      if TypeSet.is_empty family then family else
        TypeSet.add super_ty family

  (* ensure that [type_family_cast t super_ty ty] never return the empty set. *)
  let type_family_cast t super_ty ty =
    let family = type_family_cast t super_ty ty in
    if TypeSet.is_empty family then
      raise (Invalid_argument "invalid cast")
    else
      family

  (** Checks if [b] is a subtype of (or equal to) [a]. *)
  let is_subtype t a b =
    Aut.recognizes_state_in a b t.type_system

  let is_subtype_opt t a b : bool =
    match a, b with
    | Some a, Some b -> is_subtype t a b
    | _ -> true

  let compare_type_opt t a b =
    if Type.equal a b then Some 0 else
    if is_subtype t b a then Some 1 else
    if is_subtype t a b then Some (-1) else
      None

  let most_precise_type2_opt t a b =
    if is_subtype t b a then
      Some a
    else if is_subtype t a b then
      Some b
    else
      None

  let most_precise_type t span set =
    let unified_opt = Aut.StateSet.fold (
        fun ty unified_opt ->
          let unifying = Aut.StateSet.for_all (
              function ty' ->
              match most_precise_type2_opt t ty ty' with
              | Some _ -> true
              | None -> false
            ) set
          in
          if unifying then begin
            match unified_opt with
            | Some ty' -> most_precise_type2_opt t ty ty'
            | None -> Some ty
          end else unified_opt
      ) set None
    in
    begin match unified_opt with
      | Some unified -> unified
      | None ->
        Log.err (fun m -> m "unification failed");
        raise (Error (UnificationFailed set, span))
    end

  let rec compare_type_decoration_opt t (a, (tya, _)) (b, (tyb, _)) =
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

  let substitution pattern : TypedPattern.Var.t -> Aut.State.t =
    let sigma = TypedPattern.substitution pattern in
    function x -> fst (TypedPattern.Substitution.find x sigma)

  let rec as_variable = function
    | TypedPattern.Var x, (ty, span) -> Some (x, (ty, span))
    | TypedPattern.Cons _, _ -> None
    | TypedPattern.Cast pattern, _ ->
      as_variable pattern

  let rec apply_substitution sigma pattern : TypedPattern.t =
    match as_variable pattern with
    | Some (x, (ty, span)) when Type.equal ty (sigma x) ->
      pattern
    | _ ->
      begin
        match pattern with
        | TypedPattern.Var x, (ty, span) ->
          TypedPattern.Cast (TypedPattern.Var x, (sigma x, span)), (ty, span)
        | TypedPattern.Cons (f, l), (ty, span) ->
          TypedPattern.Cons (f, List.map (apply_substitution sigma) l), (ty, span)
        | TypedPattern.Cast pattern, (ty, span) ->
          TypedPattern.Cast (apply_substitution sigma pattern), (ty, span)
      end

  let is_expected expected_ty_opt ty =
    match expected_ty_opt with
    | Some expected_ty -> Aut.State.equal expected_ty ty
    | None -> true

  let constructor_symbol_signatures f ty_opt t =
    Aut.fold_transitions (
      fun conf _ ty' (sigs, t) ->
        if is_expected ty_opt ty' then begin
          match conf with
          | Aut.Configuration.Cons (f', l) when Aut.Sym.equal f f' ->
            let signature = List.map Aut.Configuration.normalized l, ty' in
            signature::sigs, t
          | Aut.Configuration.Cons (f', _) ->
            (* Log.debug (fun m -> m "! symbol missmatch %t" (Aut.Sym.print f')); *)
            sigs, t
          | _ ->
            sigs, t
        end else begin
          (* Log.debug (fun m -> m "! unexpected type %t" (Type.print ty')); *)
          sigs, t
        end
    ) t.type_system ([], t)

  let rec cast_into_opt t target_ty (pattern, (ty, span)) =
    if Aut.State.equal target_ty ty then
      Some (pattern, (ty, span))
    else
      let exception Found of TypedPattern.t in
      let _ = 0 in
      try
        let sub_types = Aut.sub_states_of t.type_system target_ty in
        Aut.StateSet.iter (
          fun sub_ty ->
            match cast_into_opt t sub_ty (pattern, (ty, span)) with
            | Some casted_pattern ->
              raise (Found (TypedPattern.Cast casted_pattern, (target_ty, span)))
            | None -> ()
        ) sub_types;
        None
      with
      | Found casted_pattern -> Some casted_pattern

  let cast_into t target_ty (pattern, (ty, span)) =
    match cast_into_opt t target_ty (pattern, (ty, span)) with
    | Some casted_pattern -> casted_pattern
    | None -> raise (Invalid_argument "invalid cast")

  let rec with_functional_symbol_signature f l_tys ty t =
    let signature = (f, l_tys, ty) in
    (* Log.debug (fun m -> m "+ trying with %t" (SymSig.print signature)); *)
    begin match SymSigTable.find_opt signature t.sig_table with
      | Some true -> t
      | Some false ->
        (* Log.debug (fun m -> m "- known to be invalid"); *)
        raise Not_found
      | None ->
        let rules, t = TypedTrs.fold (
            fun (lhs, rhs) (rules, t) ->
              match lhs with
              | TypedPattern.Cons (f', l), (ty', lhs_span) when Aut.Sym.equal f f' && is_subtype t ty' ty ->
                (* type the sub-patterns of the lhs. *)
                let typed_ls, t = List.fold_right2 (
                    fun sub_pattern ty (typed_ls, t) ->
                      let typed_sub_patterns, t = type_pattern_with ~refine_vars:true sub_pattern (Some ty) t in
                      let typed_sub_patterns = most_precise_type_decorations t typed_sub_patterns in
                      typed_sub_patterns::typed_ls, t
                  ) l l_tys ([], t)
                in
                (* Assume we can recurse... *)
                let t = { t with sig_table = SymSigTable.set signature true t.sig_table } in
                (* For each possible lhs decoration, we must be able to type the rhs with [ty]. *)
                List.fold_inline_combinations (
                  fun typed_l (rules, t) ->
                    let typed_lhs = TypedPattern.Cons (f, typed_l), (ty, lhs_span) in
                    let sigma = substitution typed_lhs in
                    match type_pattern_with (apply_substitution sigma rhs) (Some ty) t with
                    | [], t ->
                      (* Log.debug (fun m -> m "- right hand side untypable"); *)
                      raise Not_found
                    | typed_rhss, t ->
                      let typed_rhss = most_precise_type_decorations t typed_rhss in
                      begin match typed_rhss with
                        | [] -> failwith "unreachable"
                        | [typed_rhs] ->
                          TypedTrs.add (typed_lhs, typed_rhs) rules, t
                        | _ ->
                          (* Log.debug (fun m -> m "- ambiguous right hand side"); *)
                          raise (Error (Ambiguity, span_of rhs))
                      end
                ) typed_ls (rules, t)
              | _ -> rules, t
          ) t.trs (TypedTrs.empty, t)
        in
        if TypedTrs.is_empty rules then begin
          (* Log.debug (fun m -> m "- not a function"); *)
          raise Not_found
        end else
          { t with typed_trs = TypedTrs.union rules t.typed_trs }
    end

  and with_functional_symbol_signature_opt f l_tys ty_opt base_ty span t =
    begin match ty_opt with
      | Some ty ->
        begin
          try
            (* Log.debug (fun m -> m "+ trying with %t" (SymSig.print (f, l_tys, ty))); *)
            let t = with_functional_symbol_signature f l_tys ty t in
            (* Log.debug (fun m -> m "- success"); *)
            Some ty, t
          with
          | Not_found ->
            (* Log.debug (fun m -> m "- failure"); *)
            let signature = (f, l_tys, ty) in
            let t = { t with sig_table = SymSigTable.set signature false t.sig_table } in
            None, t
        end
      | None ->
        let sig_union _ a b =
          if a = b then Some a else failwith "inconsistent symbol signature table"
        in
        let ty_family = type_family t base_ty in
        (* Log.debug (fun m -> m "type family for %t(%t):%t is %t" (Aut.Sym.print f) (List.print Type.print ", " l_tys) (Type.print base_ty) (TypeSet.print ty_family)); *)
        let possibles, t = Aut.StateSet.fold (
            fun ty (possibles, t) ->
              match with_functional_symbol_signature_opt f l_tys (Some ty) base_ty span t with
              | Some _, t' ->
                ty::possibles, {
                  t with
                  typed_trs = TypedTrs.union t.typed_trs t'.typed_trs;
                  sig_table = SymSigTable.union sig_union t.sig_table t'.sig_table
                }
              | None, t -> possibles, t
          ) ty_family ([], t)
        in
        begin match possibles with
          | [] -> None, t
          | possibles ->
            let possible_tys = Aut.StateSet.of_list possibles in
            let ty = most_precise_type t span possible_tys in
            (* let t' = snd (List.find (function (ty', _) -> Aut.State.equal ty ty') possibles) in
            let t = { t' with
                      sig_table = SymSigTable.union sig_union t.sig_table t'.sig_table
                    } in *)
            Some ty, t
        end
    end

  (* If [refine_vars] is set, then a variable will be typed with all possible refinements of its type. *)
  and type_pattern_with ?(refine_vars=false) pattern ty_opt t =
    (* begin
      match ty_opt with
      | Some ty -> Log.debug (fun m -> m "+ typing %t with %t" (TypedPattern.print pattern) (Type.print ty))
      | None -> Log.debug (fun m -> m "+ typing %t" (TypedPattern.print pattern))
    end; *)
    let typed_patterns, t = match pattern with
      | TypedPattern.Var x, (found_ty, span) ->
        if is_subtype_opt t ty_opt (Some found_ty) then (* FIXME cast ! *)
          let typed_patterns =
            (* if refine_vars then
               let ty_family = match ty_opt with
                | Some ty -> type_family_cast t ty found_ty
                | None -> type_family t found_ty
               in
               Aut.StateSet.fold (
                fun ty typed_patterns ->
                  let typed_pattern = TypedPattern.Var x, (ty, span) in
                  typed_pattern::typed_patterns
               ) ty_family []
               else *)
            match ty_opt with
            | Some ty -> [cast_into t ty (TypedPattern.Var x, (found_ty, span))]
            | None -> [TypedPattern.Var x, (found_ty, span)]
          in
          typed_patterns, t
        else if refine_vars && is_subtype_opt t (Some found_ty) ty_opt then
          [TypedPattern.Var x, (Option.get ty_opt, span)], t
        else
          [], t
      | TypedPattern.Cons (f, l), (found_ty, span) ->
        if is_subtype_opt t ty_opt (Some found_ty) || is_subtype_opt t (Some found_ty) ty_opt then begin
          match constructor_symbol_signatures f ty_opt t with
          | [], t ->
            (* Log.debug (fun m -> m "i function symbol"); *)
            (* It is not a constructor symbol or it is not present in this type. *)
            (* We then type the sub-patterns without any type expectations. *)
            begin try
                let typed_ls, l_tys, t = List.fold_right (
                    fun sub_pattern (typed_ls, l_tys, t) ->
                      let typed_sub_patterns, t = type_pattern_with ~refine_vars sub_pattern None t in
                      match typed_sub_patterns with
                      | [] -> raise Not_found
                      | typed_sub_patterns ->
                        let tys = List.map type_of typed_sub_patterns in
                        let tys = TypeSet.of_list tys in
                        let ty = most_precise_type t span tys in
                        let typed_sub_patterns = List.filter (with_ty ty) typed_sub_patterns in
                        typed_sub_patterns::typed_ls, ty::l_tys, t
                  ) l ([], [], t)
                in
                match with_functional_symbol_signature_opt f l_tys ty_opt found_ty span t with
                | Some ty, t ->
                  let typed_patterns = List.fold_inline_combinations (
                      fun typed_l typed_patterns ->
                        let typed_pattern = TypedPattern.Cons (f, typed_l), (ty, span) in
                        typed_pattern::typed_patterns
                    ) typed_ls []
                  in
                  typed_patterns, t
                | None, t -> [], t
              with
              | Not_found ->
                Log.debug (fun m -> m "aborted");
                [], t
            end
          | sigs, t ->
            (* It is a constructor symbol. *)
            (* Log.debug (fun m -> m "i constructor symbol"); *)
            begin
              List.fold_right (
                fun (l_tys, ty) (typed_patterns, t) ->
                  let typed_ls, t = List.fold_right2 (
                      fun sub_pattern sub_ty (typed_ls, t) ->
                        let typed_sub_patterns, t = type_pattern_with ~refine_vars sub_pattern (Some sub_ty) t in
                        let typed_sub_patterns = most_precise_type_decorations t typed_sub_patterns in
                        typed_sub_patterns::typed_ls, t
                    ) l l_tys ([], t)
                  in
                  let typed_patterns = List.fold_inline_combinations (
                      fun typed_l typed_patterns ->
                        let typed_pattern = TypedPattern.Cons (f, typed_l), (ty, span) in
                        typed_pattern::typed_patterns
                    ) typed_ls typed_patterns
                  in
                  typed_patterns, t
              ) sigs ([], t)
            end
        end else [], t
      | TypedPattern.Cast pattern, _ ->
        type_pattern_with ~refine_vars pattern ty_opt t
    in
    (* Log.debug (fun m -> m "- [%t]" (List.print TypedPattern.print "; " typed_patterns)); *)
    typed_patterns, t

  (** Type a pattern with sub types without any output type expectations. *)
  let type_pattern pattern t =
    let typed_patterns, t = type_pattern_with pattern None t in
    match most_precise_type_decorations t typed_patterns with
    | [] -> failwith "sub-typing failed!"
    | typed_patterns -> typed_patterns, t

  let type_system t = t.type_system

  let typed_trs t = t.typed_trs

  let create aut trs =
    {
      type_system = aut;
      trs = trs;
      typed_trs = TypedTrs.empty;
      sig_table = SymSigTable.create 8
    }
end
