open Collections
open Timbuk

let log_src = Logs.Src.create "timbuk.typing.poly"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type S = sig
  module Location : sig type t end
  module Sym : AppSymbol.S
  module Base : Automaton.STATE
  module Aut : Automaton.S with type Sym.t = Sym.t and type State.t = Base.t GenericTypes.poly and type Label.t = unit
  module OptTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Base.t GenericTypes.poly option * Location.t)
  module Trs : Relation.S with type ord = OptTypedPattern.t
  module TypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Var.t = OptTypedPattern.Var.t and type Type.t = Base.t GenericTypes.poly * Location.t
  module TypedTrs : Relation.S with type ord = TypedPattern.t

  type error =
    | NonLinearLHS
    | NonNormalizedTypeAut
    | NotFunctional
    | TypeMissmatch of Base.t GenericTypes.poly * Location.t option * Base.t GenericTypes.poly
    | PatternSubtyping of Base.t GenericTypes.poly * Base.t GenericTypes.poly
    | InvalidCast of Base.t GenericTypes.poly * TypedPattern.t
    | InvalidArity of Aut.Sym.t * int * int

  exception Error of error * Location.t

  type t

  val create : Trs.t -> Aut.t -> t
  val type_system : t -> Aut.t
  val typed_trs : t -> TypedTrs.t
  val type_pattern : OptTypedPattern.t -> t -> TypedPattern.t * t

  val print_error : error -> Format.formatter -> unit
  val error_label : error -> string option
  (* val format_error_hints : error -> Location.t -> unit *)
end

module MakeRule = Rule.Make

module Make
    (Location : sig type t end)
    (Sym : AppSymbol.S)
    (Base : Automaton.STATE)
    (Aut : Automaton.S with type Sym.t = Sym.t and type State.t = Base.t GenericTypes.poly and type Label.t = unit)
    (OptTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Base.t GenericTypes.poly option * Location.t))
    (Trs : Relation.S with type ord = OptTypedPattern.t)
    (TypedTrs : Relation.S with type ord = (Sym.t, OptTypedPattern.Var.t, Base.t GenericTypes.poly * Location.t) TypedPattern.typed_pattern)
= struct
  module Location = Location
  module Sym = Sym
  module Base = Base
  module Aut = Aut
  module OptTypedPattern = OptTypedPattern
  module Trs = Trs

  module Type = GenericTypes.Poly (Base)

  module LocType = struct
    type t = Type.t * Location.t

    let compare (a, _) (b, _) =
      Type.compare a b

    let equal (a, _) (b, _) =
      Type.equal a b

    let product (a, span) (b, _) =
      match Type.product a b with
      | Some t -> Some (t, span)
      | None -> None

    let hash (t, _) =
      Type.hash t

    let print (t, _) fmt =
      Type.print t fmt
  end

  module TypedPattern = TypedPattern.Make (Aut.Sym) (OptTypedPattern.Var) (LocType)
  (* module TypedRule = MakeRule (TypedPattern) *)
  module TypedTrs = TypedTrs

  module FlowGraph = Graph.Make (Sym)
  module SymSet = FlowGraph.NodeSet
  module SymTable = HashTable.Make (Sym)

  module Var = struct
    type t = int

    let compare a b =
      a - b

    let equal a b =
      a = b

    let hash = Hashtbl.hash

    let print x fmt =
      Format.fprintf fmt "#%d" x
  end

  module VarTable = HashTable.Make (Var)

  type t = {
    trs: Trs.t;
    type_system: Aut.t;
    typed_trs: TypedTrs.t;
    var_table: Type.t VarTable.t;
    non_constr_symbols: (LocType.t list * LocType.t) SymTable.t;
    var_count: int
  }

  type error =
    | NonLinearLHS
    | NonNormalizedTypeAut
    | NotFunctional
    | TypeMissmatch of Type.t * Location.t option * Type.t
    | PatternSubtyping of Type.t * Type.t
    | InvalidCast of Type.t * TypedPattern.t
    | InvalidArity of Aut.Sym.t * int * int

  exception Error of error * Location.t

  let print_error e fmt =
    match e with
    | NonLinearLHS ->
      Format.fprintf fmt "left-hand side of functional TRS is not linear"
    | NonNormalizedTypeAut ->
      Format.fprintf fmt "type system automaton must be normalized"
    | NotFunctional ->
      Format.fprintf fmt "the given TRS is not fully functional"
    | TypeMissmatch _ ->
      Format.fprintf fmt "type missmatch"
    | PatternSubtyping _ ->
      Format.fprintf fmt "only variables can be casted to a sub-type"
    | InvalidCast _ ->
      Format.fprintf fmt "invalid cast"
    | InvalidArity _ ->
      Format.fprintf fmt "invalid number of arguments"

  let error_label e =
    match e with
    | TypeMissmatch (expected_ty, _, found_ty) ->
      let msg = Format.asprintf "expected `%t', found `%t'" (Aut.State.print expected_ty) (Aut.State.print found_ty) in
      Some msg
    | PatternSubtyping (sub, base) ->
      let msg = Format.asprintf "cast to `%t' which is a sub-type of `%t'" (Type.print sub) (Type.print base) in
      Some msg
    | InvalidCast (target_ty, (_, (ty, _))) ->
      let msg = Format.asprintf "type %t cannot be casted into %t" (Type.print ty) (Type.print target_ty) in
      Some msg
    | InvalidArity (f, 0, _) ->
      let msg = Format.asprintf "symbol `%t' requires no arguments" (Aut.Sym.print f) in
      Some msg
    | InvalidArity (f, 1, found) ->
      let msg = Format.asprintf "symbol `%t' requires 1 argument, not %d" (Aut.Sym.print f) found in
      Some msg
    | InvalidArity (f, expected, found) ->
      let msg = Format.asprintf "symbol `%t' requires %d arguments, not %d" (Aut.Sym.print f) expected found in
      Some msg
    | _ -> None

  (* let format_error_hints e fmt =
    match e with
    | TypeMissmatch (expected_ty, Some expected_span, _) ->
      let msg = Format.asprintf "type `%t' is required here" (Aut.State.print expected_ty) in
      Location.Formatter.add fmt expected_span (Some msg) Location.Formatter.Highlight.Note
    | _ -> () *)

  let new_type_var t =
    let id = t.var_count in
    let t = { t with var_count = id + 1 } in
    GenericTypes.PolyVar id, t

  let rec functional_symbol_in_lhs = function
    | TypedPattern.Cons (AppSymbol.App, e::_::[]), _ ->
      functional_symbol_in_lhs e
    | TypedPattern.Cons (f, _), _ -> f
    | _, (_, span) -> raise (Error (NotFunctional, span))

  let type_of (_, ty) = ty

  let rec without_typevar table ty =
    match ty with
    | GenericTypes.PolyVar x ->
      begin match Hashtbl.find_opt table x with
        | Some i -> GenericTypes.Polymorphic i
        | None ->
          let i = Hashtbl.length table in
          Hashtbl.add table x i;
          GenericTypes.Polymorphic i
      end
    | GenericTypes.PolyBase q -> GenericTypes.PolyBase q
    | GenericTypes.PolyFun (a, b) ->
      GenericTypes.PolyFun (without_typevar table a, without_typevar table b)
    | GenericTypes.Polymorphic _ -> ty

  let register_nonconstructor_type f sub_tys ty t =
    (* Log.debug (fun m -> m "register %t" (Sym.print f)); *)
    { t with non_constr_symbols = SymTable.set f (sub_tys, ty) t.non_constr_symbols }

  let is_subtype t ty =
    not (Aut.is_final t.type_system ty)

  let rec base_type_of t ty =
    if not (is_subtype t ty) then ty else
      let conf : Aut.Configuration.t = Aut.Configuration.Var ty in
      let super_types = Aut.states_for_configuration conf t.type_system in
      let super_ty, _ = Aut.LabeledStateSet.choose super_types in
      base_type_of t super_ty

  let constructor_signature t f =
    begin match f with
      | AppSymbol.App ->
        let ty_a, t = new_type_var t in
        let ty_r, t = new_type_var t in
        let ty_f = GenericTypes.PolyFun (ty_a, ty_r) in
        Some ([ty_f; ty_a], ty_r, t)
      | f ->
        let exception Found of Type.t list * Type.t in
        let _ = 0 in (* for the syntax coloration in Atom... *)
        begin try
            Aut.fold_transitions (
              fun conf _ ty () ->
                if is_subtype t ty then () else
                  match conf with
                  | Aut.Configuration.Cons (f', l) when Aut.Sym.equal f f' ->
                    let as_type = function
                      | Aut.Configuration.Var ty -> ty
                      | _ -> raise (Invalid_argument "not normalized")
                    in
                    let expected_sub_tys = List.map as_type l in
                    raise (Found (expected_sub_tys, ty))
                  | _ -> ()
            ) t.type_system ();
            None
          with
          | Found (expected_sub_tys, ty) -> Some (expected_sub_tys, ty, t)
        end
    end

  let symbol_signature t f =
    let some_span (ty, span) = (ty, Some span) in
    let no_span ty = (ty, None) in
    match constructor_signature t f with
    | Some (expected_sub_tys, expected_ty, t) -> Some (List.map no_span expected_sub_tys, no_span expected_ty, t)
    | None ->
      begin match SymTable.find_opt f t.non_constr_symbols with
        | Some (expected_sub_tys, expected_ty) -> Some (List.map some_span expected_sub_tys, some_span expected_ty, t)
        | None -> None
      end

  let rec remove_typevar sigma = function
    | GenericTypes.PolyVar x -> sigma x
    | GenericTypes.Polymorphic i -> GenericTypes.Polymorphic i
    | GenericTypes.PolyBase q -> GenericTypes.PolyBase q
    | GenericTypes.PolyFun (a, b) -> GenericTypes.PolyFun (remove_typevar sigma a, remove_typevar sigma b)

  let remove_loc_typevar sigma (ty, span) = (remove_typevar sigma ty, span)

  let rec remove_typevar_in_pattern sigma pattern =
    (* Log.debug (fun m -> m "remove typevar from %t" (TypedPattern.print pattern)); *)
    match pattern with
    | TypedPattern.Var x, (ty, span) ->
      TypedPattern.Var x, (remove_typevar sigma ty, span)
    | TypedPattern.Cons (f, l), (ty, span) ->
      TypedPattern.Cons (f, List.map (remove_typevar_in_pattern sigma) l), (remove_typevar sigma ty, span)
    | TypedPattern.Cast sub, (ty, span) ->
      TypedPattern.Cast (remove_typevar_in_pattern sigma sub), (remove_typevar sigma ty, span)

  let rec remove_poly_from_ty table ty t =
    match ty with
    | GenericTypes.Polymorphic i ->
      begin match Hashtbl.find_opt table i with
        | Some ty -> ty, t
        | None ->
          let ty, t = new_type_var t in
          Hashtbl.add table i ty;
          ty, t
      end
    | GenericTypes.PolyFun (a, b) ->
      let a, t = remove_poly_from_ty table a t in
      let b, t = remove_poly_from_ty table b t in
      GenericTypes.PolyFun (a, b), t
    | _ -> ty, t

  let remove_poly_from_loc_ty table (ty, span) t =
    let ty, t = remove_poly_from_ty table ty t in
    (ty, span), t

  let remove_poly_from_signature subs ty t =
    let table = Hashtbl.create 8 in
    let subs, t = List.fold_right (
        fun ty (subs, t) ->
          let ty, t = remove_poly_from_loc_ty table ty t in
          ty::subs, t
      ) subs ([], t)
    in
    let ty, t = remove_poly_from_loc_ty table ty t in
    subs, ty, t

  let rec reduce_type t ty =
    match ty with
    | GenericTypes.PolyVar x ->
      begin match VarTable.find_opt x t.var_table with
        | Some ty' -> reduce_type t ty'
        | None -> GenericTypes.PolyVar x
      end
    | GenericTypes.PolyBase q -> GenericTypes.PolyBase q
    | GenericTypes.PolyFun (a, b) ->
      GenericTypes.PolyFun (reduce_type t a, reduce_type t b)
    | GenericTypes.Polymorphic _ -> raise (Invalid_argument "cannot reduce polymorphic type")

  let rec reduce_pattern t = function
    | TypedPattern.Var x, (ty, span) ->
      TypedPattern.Var x, (reduce_type t ty, span)
    | TypedPattern.Cons (f, l), (ty, span) ->
      TypedPattern.Cons (f, List.map (reduce_pattern t) l), (reduce_type t ty, span)
    | TypedPattern.Cast sub, (ty, span) ->
      TypedPattern.Cast (reduce_pattern t sub), (reduce_type t ty, span)

  let rec functional_symbol_type_in = function
    | TypedPattern.Cons (AppSymbol.App, e::_::[]), _ ->
      functional_symbol_type_in e
    | TypedPattern.Cons (_, subs), ty -> (List.map type_of subs, ty)
    | _, (_, span) -> raise (Error (NotFunctional, span))

  let vartype_substitution pattern =
    let table = Hashtbl.create 8 in
    let count = ref 0 in
    let next_id () =
      let id = !count in
      count := id + 1;
      id
    in
    let rec erase_typevar = function
      | GenericTypes.PolyVar x ->
        begin
          match Hashtbl.find_opt table x with
          | Some _ -> ()
          | None ->
            Hashtbl.add table x (next_id ())
        end
      | GenericTypes.PolyFun (a, b) ->
        erase_typevar a;
        erase_typevar b
      | _ -> ()
    in
    TypedPattern.iter (function (_, (ty, _)) -> erase_typevar ty) pattern;
    function x ->
      begin match Hashtbl.find_opt table x with
        | Some i -> GenericTypes.Polymorphic i
        | None ->
          Log.err (fun m -> m "unable to erase type variable %t in pattern %t" (Aut.State.print (GenericTypes.PolyVar x)) (TypedPattern.print pattern));
          failwith "unable to erase type variable"
      end

  let reduce_rule t (l, r) =
    let (l, r) = reduce_pattern t l, reduce_pattern t r in
    (* Remove global variables. *)
    let sigma = vartype_substitution l in
    (* Log.debug (fun m -> m "remove vars from %t -> %t" (TypedPattern.print l) (TypedPattern.print r)); *)
    let l, r = remove_typevar_in_pattern sigma l, remove_typevar_in_pattern sigma r in
    let (subs, ty) = functional_symbol_type_in l in
    let t = register_nonconstructor_type (functional_symbol_in_lhs l) subs ty t in
    (* Log.debug (fun m -> m "typed rule %t -> %t" (TypedPattern.print l) (TypedPattern.print r)); *)
    (l, r), t

  let substitute x ty t =
    { t with var_table = VarTable.set x ty t.var_table }

  let rec unify_opt_span_core (expected_ty, expected_span_opt) (found_ty, found_span) t =
    (* Log.debug (fun m -> m "unify %t and %t" (Aut.State.print expected_ty) (Aut.State.print found_ty)); *)
    let expected_ty = reduce_type t expected_ty in
    let found_ty = reduce_type t found_ty in
    match expected_ty, found_ty with
    | GenericTypes.PolyVar a, GenericTypes.PolyVar b ->
      if a = b then t else
      if a < b then substitute b (GenericTypes.PolyVar a) t else substitute a (GenericTypes.PolyVar b) t
    | GenericTypes.PolyVar a, found_ty -> substitute a found_ty t
    | expected_ty, GenericTypes.PolyVar b -> substitute b expected_ty t
    | GenericTypes.PolyBase e, GenericTypes.PolyBase f when Base.equal e f -> t
    | GenericTypes.PolyFun (e1, e2), GenericTypes.PolyFun (f1, f2) ->
      unify_opt_span_core (e2, expected_span_opt) (f2, found_span) (unify_opt_span_core (e1, expected_span_opt) (f1, found_span) t)
    | GenericTypes.Polymorphic _, _ | _, GenericTypes.Polymorphic _ ->
      raise (Invalid_argument "cannot unify polymorphic type")
    | _ ->
      raise (Error (TypeMissmatch (expected_ty, expected_span_opt, found_ty), found_span))

  let unify_opt_span (expected_ty, expected_span_opt) (found_ty, found_span) t =
    try unify_opt_span_core (expected_ty, expected_span_opt) (found_ty, found_span) t with
    | Error (TypeMissmatch _, _) ->
      let table = Hashtbl.create 8 in
      let expected_ty = without_typevar table (reduce_type t expected_ty) in
      let found_ty = without_typevar table (reduce_type t found_ty) in
      raise (Error (TypeMissmatch (expected_ty, expected_span_opt, found_ty), found_span))

  let unify (expected_ty, expected_span) (found_ty, found_span) t =
    unify_opt_span (expected_ty, Some expected_span) (found_ty, found_span) t

  let unify_no_span expected_ty (found_ty, found_span) t =
    unify_opt_span (expected_ty, None) (found_ty, found_span) t

  let unify_cast (cast_opt, span) ty t =
    match cast_opt with
    | Some cast -> unify (cast, span) ty t
    | None -> t

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
    | None -> raise (Error (InvalidCast (target_ty, (pattern, (ty, span))), span))

  let rec type_pattern (pattern : OptTypedPattern.t) (t : t) =
    (* Log.debug (fun m -> m "+ typing pattern %t" (OptTypedPattern.print pattern)); *)
    let typed_pattern, t = match pattern with
      | OptTypedPattern.Var x, (Some cast, span) when is_subtype t cast ->
        let base_ty = base_type_of t cast in
        let ty, t = new_type_var t in
        let ty = ty, span in
        let t = unify_cast (Some base_ty, span) ty t in
        cast_into t base_ty (TypedPattern.Var x, (cast, span)), t
      | _, (Some cast, span) when is_subtype t cast ->
        let base_ty = base_type_of t cast in
        raise (Error (PatternSubtyping (cast, base_ty), span))
      | OptTypedPattern.Var x, (cast_opt, span) ->
        let ty, t = new_type_var t in
        let ty = ty, span in
        let t = unify_cast (cast_opt, span) ty t in
        (TypedPattern.Var x, ty), t
      | OptTypedPattern.Cons (f, l), (cast_opt, span) ->
        let typed_l, t = List.fold_right (
            fun sub_pattern (typed_l, t) ->
              let typed_pattern, t = type_pattern sub_pattern t in
              typed_pattern::typed_l, t
          ) l ([], t)
        in
        begin match symbol_signature t f with
          | Some (expected_sub_tys, ty, t) ->
            let arity = List.length expected_sub_tys in
            let l_len = List.length typed_l in
            if arity <> l_len then
              raise (Error (InvalidArity (f, arity, l_len), span));
            let expected_sub_tys, (ty, _), t = remove_poly_from_signature expected_sub_tys ty t in
            let t = List.fold_right2 (
                fun expected_sub_ty (_, sub_ty) t ->
                  unify_opt_span expected_sub_ty sub_ty t
              ) expected_sub_tys typed_l t
            in
            let t = unify_cast (cast_opt, span) (ty, span) t in
            (TypedPattern.Cons (f, typed_l), (ty, span)), t
          | None ->
            let ty, t = new_type_var t in
            let ty = ty, span in
            let sub_tys = List.map type_of typed_l in
            let t = register_nonconstructor_type f sub_tys ty t in
            let t = unify_cast (cast_opt, span) ty t in
            (TypedPattern.Cons (f, typed_l), ty), t
        end
      | OptTypedPattern.Cast _, _ ->
        raise (Invalid_argument "casts are not handled")
    in
    (* Log.debug (fun m -> m "- %t" (TypedPattern.print typed_pattern)); *)
    typed_pattern, t

  let type_rule (l, r) t =
    (* Log.debug (fun m -> m "typing rule %t -> %t" (OptTypedPattern.print l) (OptTypedPattern.print r)); *)
    let typed_l, t = type_pattern l t in
    let typed_r, t = type_pattern r t in
    let ty_l = type_of typed_l in
    let ty_r = type_of typed_r in
    let t = unify ty_l ty_r t in
    let sigma_opt = TypedPattern.fold (
        fun pattern sigma ->
          match pattern with
          | TypedPattern.Var x, ty ->
            begin match sigma x with
              | None -> (function y -> if TypedPattern.Var.equal x y then Some ty else sigma y)
              | Some _ -> failwith "not left-linear"
            end
          | _ -> sigma
      ) typed_l (function _ -> None)
    in
    let sigma x =
      match sigma_opt x with
      | Some ty -> ty
      | None -> failwith "undefined variable"
    in
    let t = TypedPattern.fold (
        fun pattern t ->
          match pattern with
          | TypedPattern.Var x, ty ->
            unify (sigma x) ty t
          | _ -> t
      ) typed_r t
    in
    (typed_l, typed_r), t

  (** Add irreducible higher-order terms to the type-system automaton. *)
  let extract_ho_types typed_rules t =
    let type_of (_, (ty, _)) = ty in
    let rec extract_from pattern aut =
      match pattern with
      | TypedPattern.Cons (AppSymbol.App, a::b::[]), (ty, _) ->
        let aut = extract_from a aut in
        let l_types = List.map type_of (a::b::[]) in
        let conf = Aut.Configuration.Cons (AppSymbol.App, List.map Aut.Configuration.of_var l_types) in
        Aut.add_transition conf () ty (Aut.add_final_state ty aut)
      | TypedPattern.Cons (f, l), (ty, _) ->
        let l_types = List.map type_of l in
        let conf = Aut.Configuration.Cons (f, List.map Aut.Configuration.of_var l_types) in
        Aut.add_transition conf () ty (Aut.add_final_state ty aut)
      | _ -> aut
    in
    let aut = TypedTrs.fold (
        fun (lhs, _) aut ->
          match lhs with
          | TypedPattern.Cons (AppSymbol.App, e::_::[]), _ ->
            extract_from e aut
          | _ -> aut
      ) typed_rules t.type_system
    in
    { t with type_system = aut }

  (** Type a functional symbol definition. *)
  let type_component_definition component t =
    (* Log.debug (fun m -> m "typing component {%t}" (SymSet.print Sym.print ", " component)); *)
    let defines f (lhs, _) = Sym.equal f (functional_symbol_in_lhs lhs) in
    let typed_rules, t = SymSet.fold (
        fun f (typed_rules, t) ->
          let rules = Trs.filter (defines f) t.trs in
          Trs.fold (
            fun rule (typed_rules, t) ->
              let typed_rule, t = type_rule rule t in
              TypedTrs.add typed_rule typed_rules, t
          ) rules (typed_rules, t)
      ) component (TypedTrs.empty, t)
    in
    (* Log.debug (fun m -> m "before reduction:\n%t" (TypedTrs.print typed_rules)); *)
    let typed_rules, t = TypedTrs.fold (
        fun rule (rules, t) ->
          let reduced_rule, t = reduce_rule t rule in
          TypedTrs.add reduced_rule rules, t
      ) typed_rules (TypedTrs.empty, t)
    in
    (* Log.debug (fun m -> m "poly typed TRS:\n%t" (TypedTrs.print typed_rules)); *)
    let t = extract_ho_types typed_rules t in
    { t with typed_trs = TypedTrs.union typed_rules t.typed_trs }

  let rec called_functions t = function
    | TypedPattern.Var x, _ -> SymSet.empty
    | TypedPattern.Cons (f, l), _ ->
      let funs = List.fold_right (
          fun sub funs ->
            SymSet.union (called_functions t sub) funs
        ) l SymSet.empty
      in
      begin match constructor_signature t f with
        | Some _ -> funs
        | None -> SymSet.add f funs
      end
    | TypedPattern.Cast sub, _ -> called_functions t sub

  (** Build the flow graph of the TRS. *)
  let flow_graph t =
    Trs.fold (
      fun (lhs, rhs) flow_graph ->
        let f = functional_symbol_in_lhs lhs in
        let flow_graph = FlowGraph.add f flow_graph in
        SymSet.fold (function f' -> FlowGraph.connect f' f) (called_functions t rhs) flow_graph
    ) t.trs FlowGraph.empty

  let create trs type_system =
    let t = {
      trs = trs;
      type_system = type_system;
      typed_trs = TypedTrs.empty;
      var_table = VarTable.create 8;
      non_constr_symbols = SymTable.create 8;
      var_count = 0
    }
    in
    let flow_graph = flow_graph t in
    let module ComponentsGraph = Graph.Make (SymSet) in
    let components_graph = FlowGraph.components_graph flow_graph (module ComponentsGraph) in
    let components_scheduling = ComponentsGraph.scheduling components_graph in
    (* Log.debug (fun m -> m "scheduling is\n%t" (List.print (SymSet.print Sym.print ",") "\n" components_scheduling)); *)
    List.fold_right type_component_definition (List.rev components_scheduling) t

  let type_system t =
    t.type_system

  let typed_trs t =
    t.typed_trs

  let type_pattern pattern t =
    let typed_pattern, t = type_pattern pattern t in
    let typed_pattern = reduce_pattern t typed_pattern in
    let sigma = vartype_substitution typed_pattern in
    let typed_pattern = remove_typevar_in_pattern sigma typed_pattern in
    typed_pattern, t
end
