open Timbuk

let log_src = Logs.Src.create "timbuk.typing.mono"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type S = sig
  module Location : sig type t end

  (** Functional sympols. *)
  module Sym : AppSymbol.S

  (** Monomorphic type. *)
  module Mono : MonoType.S

  (** Polymorphic type to monomorphize. *)
  module Poly : PolyType.S with type mono = Mono.t

  (** Automaton storing the polymorphic type system. *)
  module PolyAut : Automaton.S with type Sym.t = Sym.t and type State.t = Poly.t

  (** Polymorphic pattern. *)
  module PolyTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Poly.t * Location.t)

  (** Polymorphic TRS. *)
  module PolyTypedTrs : Relation.S with type ord = PolyTypedPattern.t

  (** Monomorphic type system. *)
  module MonoAut : Automaton.S with type Sym.t = Sym.t * Mono.t list * Mono.t and type State.t = Mono.t and type Label.t = PolyAut.Label.t

  (** Typed pattern (spans are dropped). *)
  module MonoTypedPattern : TypedPattern.S with type Sym.t = MonoAut.Sym.t and type Var.t = PolyTypedPattern.Var.t and type Type.t = (Mono.t * Location.t)

  (** Typed TRS. *)
  module MonoTypedTrs : Relation.S with type ord = MonoTypedPattern.t

  (** Possible type errors. *)
  type error =
    | PolymorphicType of Poly.t

  (** Typing error. *)
  exception Error of error * Location.t

  (** Typing context, containing the current abstraction. *)
  type t

  val create : ?constant_refiner:(MonoAut.Configuration.t -> (MonoAut.State.t * MonoAut.Label.t * MonoAut.Label.t)) -> PolyTypedTrs.t -> PolyAut.t -> t

  val type_system : t -> MonoAut.t

  val typed_trs : t -> MonoTypedTrs.t

  val type_pattern : PolyTypedPattern.t -> t -> MonoTypedPattern.t * t

  val print_error : error -> Format.formatter -> unit

  val error_label : error -> string option

  (* val format_error_hints : error -> Location.Formatter.t -> unit *)
end

module Make
    (Location : sig type t end)
    (Sym : AppSymbol.S)
    (Mono : MonoType.S)
    (Poly : PolyType.S with type mono = Mono.t)
    (PolyAut : Automaton.S with type Sym.t = Sym.t and type State.t = Poly.t)
    (PolyTypedPattern : TypedPattern.S with type Sym.t = Sym.t and type Type.t = (Poly.t * Location.t))
    (PolyTypedTrs : Relation.S with type ord = PolyTypedPattern.t)
    (MonoAut : Automaton.S with type Sym.t = Sym.t * Mono.t list * Mono.t and type State.t = Mono.t and type Label.t = PolyAut.Label.t and type data = unit)
    (MonoTypedPattern : TypedPattern.S with type Sym.t = MonoAut.Sym.t and type Var.t = PolyTypedPattern.Var.t and type Type.t = (Mono.t * Location.t))
    (MonoTypedTrs : Relation.S with type ord = MonoTypedPattern.t)
= struct
  module Location = Location
  module Sym = Sym
  module Mono = Mono
  module Poly = Poly
  module PolyAut = PolyAut
  module PolyTypedPattern = PolyTypedPattern
  module PolyTypedTrs = PolyTypedTrs
  module MonoAut = MonoAut
  module MonoTypedPattern = MonoTypedPattern
  module MonoTypedTrs = MonoTypedTrs

  module MonoSymSet = Set.Make (MonoAut.Sym)

  (** Possible type errors. *)
  type error =
    | PolymorphicType of Poly.t

  (** Typing error. *)
  exception Error of error * Location.t

  type t = {
    poly_typed_trs: PolyTypedTrs.t;
    poly_type_system: PolyAut.t;
    mono_typed_trs: MonoTypedTrs.t;
    mono_type_system: MonoAut.t;
    mono_symbols: MonoSymSet.t;
    constant_refiner: (MonoAut.Configuration.t -> (MonoAut.State.t * MonoAut.Label.t * MonoAut.Label.t)) option
  }

  let create ?constant_refiner poly_typed_trs poly_aut =
    {
      poly_typed_trs = poly_typed_trs;
      poly_type_system = poly_aut;
      mono_typed_trs = MonoTypedTrs.empty;
      mono_type_system = MonoAut.create ();
      mono_symbols = MonoSymSet.empty;
      constant_refiner = constant_refiner
    }

  let type_system t =
    t.mono_type_system

  let typed_trs t =
    t.mono_typed_trs

  let type_of (_, (ty, _)) = ty

  let is_subtype t ty =
    not (MonoAut.is_final t.mono_type_system ty)

  let is_poly_subtype t ty =
    not (PolyAut.is_final t.poly_type_system ty)

  (* let rec base_type_of t ty =
     if not (is_subtype t ty) then ty else
      let conf : MonoAut.Configuration.t = MonoAut.Configuration.Var ty in
      let super_types = MonoAut.states_for_configuration conf t.mono_type_system in
      match MonoAut.LabeledStateSet.cardinal super_types with
      | 0 ->
        Log.err (fun m -> m "type %t has no super type" (MonoAut.State.print ty));
        raise (Invalid_argument "invalid sub-typing informations")
      | 1 ->
        let super_ty, _ = MonoAut.LabeledStateSet.choose super_types in
        base_type_of t super_ty
      | _ ->
        raise (Invalid_argument "ambiguous sub-typing") *)
  let rec base_type_of t ty =
    if not (is_subtype t ty) then ty else
      let conf : MonoAut.Configuration.t = MonoAut.Configuration.Var ty in
      let super_types = MonoAut.states_for_configuration conf t.mono_type_system in
      let super_ty, _ = MonoAut.LabeledStateSet.choose super_types in
      base_type_of t super_ty

  let rec base_poly_type_of t ty =
    if not (is_poly_subtype t ty) then ty else
      let conf : PolyAut.Configuration.t = PolyAut.Configuration.Var ty in
      let super_types = PolyAut.states_for_configuration conf t.poly_type_system in
      let super_ty, _ = PolyAut.LabeledStateSet.choose super_types in
      base_poly_type_of t super_ty

  let base_sig t (f, l, ty) =
    (f, List.map (base_type_of t) l, base_type_of t ty)

  (* Instanciate a polymorphic type into a monomorphic type using the given type substitution [sigma]. *)
  let rec mono_type_opt_span sigma ty span_opt =
    match Poly.destruct ty with
    | PolyType.Poly i ->
      begin try sigma i with
        | Not_found ->
          begin match span_opt with
            | Some span -> raise (Error (PolymorphicType ty, span))
            | None -> raise (Invalid_argument "inconsistent types")
          end
      end
    | PolyType.Base q -> Mono.construct (MonoType.Base (Poly.monomorphic q))
    | PolyType.Fun (a, b) ->
      begin try
          let mono_a = mono_type_opt_span sigma a span_opt in
          let mono_b = mono_type_opt_span sigma b span_opt in
          Mono.construct (MonoType.Fun (mono_a, mono_b))
        with
        | Error (PolymorphicType _, span) -> raise (Error (PolymorphicType ty, span))
      end

  let mono_type sigma ty span =
    mono_type_opt_span sigma ty (Some span)

  let mono_type_no_span sigma ty =
    mono_type_opt_span sigma ty None

  (* Compute the type substitution so that [poly_ty] matches [mono_ty]. *)
  let matches_poly_type poly_ty mono_ty =
    let table = Hashtbl.create 8 in
    let rec populate_with poly_ty mono_ty =
      match (Poly.destruct poly_ty), (Mono.destruct mono_ty) with
      | PolyType.Poly i, mono_ty -> Hashtbl.add table i (Mono.construct mono_ty)
      | PolyType.Base a, MonoType.Base b ->
        if Mono.equal (Poly.monomorphic a) b then () else raise Not_found
      | PolyType.Fun (poly_a, poly_b), MonoType.Fun (mono_a, mono_b) ->
        populate_with poly_a mono_a; populate_with poly_b mono_b
      | _ -> raise Not_found
    in
    try
      populate_with poly_ty mono_ty;
      Some (function x -> Hashtbl.find table x)
    with
    | Not_found -> None

  (* Compute the type substitution so that the given polymorphic signature matches the given monomorphic signature. *)
  let matches_poly_signature (poly_sub_tys, poly_ty) (mono_sub_ty, mono_ty) =
    let table = Hashtbl.create 8 in
    let rec populate_with poly_ty mono_ty =
      match (Poly.destruct poly_ty), (Mono.destruct mono_ty) with
      | PolyType.Poly i, mono_ty -> Hashtbl.add table i (Mono.construct mono_ty)
      | PolyType.Base a, MonoType.Base b ->
        if Mono.equal (Poly.monomorphic a) b then () else raise Not_found
      | PolyType.Fun (poly_a, poly_b), MonoType.Fun (mono_a, mono_b) ->
        populate_with poly_a mono_a; populate_with poly_b mono_b
      | _ -> raise Not_found
    in
    try
      List.iter2 populate_with poly_sub_tys mono_sub_ty;
      populate_with poly_ty mono_ty;
      Some (function x -> Hashtbl.find table x)
    with
    | Not_found -> None

  let include_mono_type ty t =
    let table = Hashtbl.create 8 in
    let visit ty =
      match Hashtbl.find_opt table ty with
      | Some () -> false
      | None ->
        Hashtbl.add table ty ();
        true
    in
    let rec do_include ty aut =
      if visit ty then begin
        PolyAut.fold_transitions (
          fun conf label poly_ty aut ->
            match matches_poly_type poly_ty ty with
            | Some sigma ->
              let aut = if PolyAut.is_final t.poly_type_system poly_ty then MonoAut.add_final_state ty aut else aut in
              let mono_conf, aut = match conf with
                | PolyAut.Configuration.Var poly_ty' ->
                  let ty' = mono_type_no_span sigma poly_ty' in
                  let aut = do_include ty' aut in
                  MonoAut.Configuration.Var ty', aut
                | PolyAut.Configuration.Cons (f, l) ->
                  let base_ty = mono_type_no_span sigma (base_poly_type_of t poly_ty) in
                  let l = List.map PolyAut.Configuration.normalized l in
                  let mono_l = List.map (mono_type_no_span sigma) l in
                  let aut = List.fold_right do_include mono_l aut in
                  MonoAut.Configuration.Cons ((f, mono_l, base_ty), List.map MonoAut.Configuration.of_var mono_l), aut
              in
              MonoAut.add_transition mono_conf label ty aut
            | None -> aut
        ) t.poly_type_system aut
      end else aut
    in
    let aut = do_include ty t.mono_type_system in
    { t with mono_type_system = aut }

  let rec poly_lhs_functional_symbol = function
    | PolyTypedPattern.Cons (AppSymbol.App, e::_::[]), _ ->
      poly_lhs_functional_symbol e
    | PolyTypedPattern.Cons (f, subs), (ty, _) ->
      let sub_tys = List.map type_of subs in
      f, sub_tys, ty
    | _, (_, span) -> raise (Invalid_argument "non functional TRS")

  let rec mono_lhs_functional_symbol : MonoTypedPattern.t -> MonoAut.Sym.t = function
    | MonoTypedPattern.Cons ((AppSymbol.App, _, _), e::_::[]), _ ->
      mono_lhs_functional_symbol e
    | MonoTypedPattern.Cons (f, subs), _ ->
      f
    | _, (_, span) -> raise (Invalid_argument "non functional TRS")

  (* let includes_mono_symbol f t =
     MonoTypedTrs.exists (
      function (lhs, _) ->
        let f' = mono_lhs_functional_symbol lhs in
        MonoAut.Sym.equal f f'
     ) t.mono_typed_trs *)

  let is_functional t f ty =
    let confs = MonoAut.configurations_for_state ty t.mono_type_system in
    MonoAut.LabeledConfigurationSet.for_all (
      function (conf, _) ->
      match conf with
      | MonoAut.Configuration.Cons (f', _) ->
        not (MonoAut.Sym.equal f f')
      | _ -> true
    ) confs

  let refine_constants_from ?(app_only=false) pattern t =
    match t.constant_refiner with
    | Some refiner ->
      let non_epsilon = function
        | MonoAut.Configuration.Cons _, _ -> true
        | _ -> false
      in
      let add_configuration is_functional conf base_ty aut =
        let states = MonoAut.states_for_configuration conf aut in
        let is_normal_parent (q, _) =
          (* Log.debug (fun m -> m "is %t normal for %t?" (MonoAut.State.print q) (MonoAut.Configuration.print conf)); *)
          let confs = MonoAut.LabeledConfigurationSet.filter non_epsilon (MonoAut.configurations_for_state q aut) in
          MonoAut.LabeledConfigurationSet.cardinal confs = 1
        in
        match MonoAut.LabeledStateSet.search_opt is_normal_parent states with
        | Some (q, _) -> Some q, aut
        | None ->
          (* if is_functional then base_ty, aut else *)
          if is_functional then None, aut else (* For now *)
            let q, label, subtyping_label = refiner conf in
            let aut = MonoAut.add_transition conf label q aut in
            let aut = MonoAut.add_transition (MonoAut.Configuration.Var q) subtyping_label base_ty aut in
            Some q, aut
      in
      let rec add_pattern allow_variables pattern base_ty aut =
        match pattern with
        | MonoTypedPattern.Var x, (ty, _) ->
          if allow_variables then
            Some ty, aut
          else
            None, aut
        | MonoTypedPattern.Cons ((AppSymbol.App, fl, fty), e::a::[]), (ty, span) when app_only ->
          let f = AppSymbol.App, fl, fty in
          begin match add_pattern allow_variables e base_ty aut with
            | Some ety, aut ->
              let lq = ety::(type_of a)::[] in
              let conf = MonoAut.Configuration.Cons (f, List.map MonoAut.Configuration.of_var lq) in
              add_configuration true conf base_ty aut
            | None, aut -> None, aut
          end
        | MonoTypedPattern.Cons (f, l), (ty, span) ->
          let is_fun = is_functional t f base_ty in
          let lq, is_complete, aut = List.fold_right (
              fun sub_pattern (lq, is_complete, aut) ->
                match add_pattern (allow_variables && not is_fun) sub_pattern (type_of sub_pattern) aut with
                | Some q, aut -> q::lq, is_complete, aut
                | None, aut -> lq, false, aut
            ) l ([], true, aut)
          in
          if is_complete then
            let conf = MonoAut.Configuration.Cons (f, List.map MonoAut.Configuration.of_var lq) in
            add_configuration is_fun conf base_ty aut
          else None, aut
        | MonoTypedPattern.Cast pattern, _ when not app_only ->
          add_pattern allow_variables pattern base_ty aut
        | _ -> None, aut
      in
      let _, aut = add_pattern true pattern (type_of pattern) t.mono_type_system in
      { t with mono_type_system = aut }
    | None -> t

  let (>>) f g =
    function x -> g (f x)

  let rec monomorphize_pattern ?(refine_consts=true) sigma pattern t =
    let rec monomorphize pattern t =
      begin match pattern with
        | PolyTypedPattern.Var x, (ty, span) ->
          let mono_ty = mono_type sigma ty span in
          let t = include_mono_type mono_ty t in
          (MonoTypedPattern.Var x, (mono_ty, span)), t
        | PolyTypedPattern.Cons (f, l), (ty, span) ->
          let typed_l, t = List.fold_right (
              fun sub_pattern (typed_l, t) ->
                let typed_sub_pattern, t = monomorphize sub_pattern t in
                let _, (mono_ty, _) = typed_sub_pattern in
                let t = include_mono_type mono_ty t in
                typed_sub_pattern::typed_l, t
            ) l ([], t)
          in
          let l_mono_tys = List.map type_of typed_l in
          let mono_ty = mono_type sigma ty span in
          let t = include_mono_type mono_ty t in
          let typed_f : MonoTypedPattern.Sym.t = f, l_mono_tys, mono_ty in
          let t : t = include_mono_symbol typed_f t in
          (MonoTypedPattern.Cons (typed_f, typed_l), (mono_ty, span)), t
        | PolyTypedPattern.Cast pattern, (ty, span) ->
          let typed_pattern, t = monomorphize pattern t in
          let mono_ty = mono_type sigma ty span in
          let t = include_mono_type mono_ty t in
          (MonoTypedPattern.Cast typed_pattern, (mono_ty, span)), t
      end
    in
    let mono_pattern, t = monomorphize pattern t in
    (* let t = if refine_consts then refine_constants_from mono_pattern t else t in *)
    mono_pattern, t

  and include_mono_symbol (f, sub_tys, ty) t =
    if MonoSymSet.mem (f, sub_tys, ty) t.mono_symbols then t else
      let t = { t with mono_symbols = MonoSymSet.add (f, sub_tys, ty) t.mono_symbols } in
      PolyTypedTrs.fold (
        fun (poly_lhs, poly_rhs) t ->
          let f', poly_sub_tys, poly_ty = poly_lhs_functional_symbol poly_lhs in
          if Sym.equal f f' then begin
            match matches_poly_signature (poly_sub_tys, poly_ty) (sub_tys, ty) with
            | Some sigma ->
              let lhs, t = monomorphize_pattern ~refine_consts:false sigma poly_lhs t in
              let rhs, t = monomorphize_pattern sigma poly_rhs t in
              { t with mono_typed_trs = MonoTypedTrs.add (lhs, rhs) t.mono_typed_trs }
            | None -> raise (Invalid_argument "inconsistent types")
          end else t
      ) t.poly_typed_trs t

  let type_pattern (pattern : PolyTypedPattern.t) (t : t) : MonoTypedPattern.t * t =
    let sigma x = raise Not_found in
    let mono_pattern, t = monomorphize_pattern sigma pattern t in
    let aut = MonoAut.fold_transitions (
        fun conf label ty aut ->
          let conf = match conf with
            | MonoAut.Configuration.Cons (f, l) ->
              MonoAut.Configuration.Cons (base_sig t f, l)
            | _ -> conf
          in
          MonoAut.add_transition conf label ty aut
      ) t.mono_type_system (MonoAut.create ())
    in
    let rec lift = function
      | MonoTypedPattern.Var x, ty ->
        MonoTypedPattern.Var x, ty
      | MonoTypedPattern.Cons (f, l), ty ->
        MonoTypedPattern.Cons (base_sig t f, List.map lift l), ty
      | MonoTypedPattern.Cast pattern, ty ->
        MonoTypedPattern.Cast (lift pattern), ty
    in
    let mono_pattern = lift mono_pattern in
    let trs = MonoTypedTrs.map (
        fun (lhs, rhs) ->
          lift lhs, lift rhs
      ) t.mono_typed_trs
    in
    let t = { t with mono_type_system = aut; mono_typed_trs = trs } in
    let t = MonoTypedTrs.fold (
        fun (lhs, rhs) t ->
          let t = refine_constants_from ~app_only:true lhs t in
          refine_constants_from rhs t
      ) t.mono_typed_trs t
    in
    let t = refine_constants_from mono_pattern t in
    mono_pattern, t

  let print_error e fmt =
    match e with
    | PolymorphicType _ -> Format.fprintf fmt "initial pattern must be monomorphic"

  let error_label e =
    match e with
    | PolymorphicType ty ->
      let msg = Format.asprintf "this has the polymorphic type `%t'" (PolyAut.State.print ty) in
      Some msg

  (* let format_error_hints e fmt =
     () *)
end
