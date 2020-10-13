open Collections
open Timbuk
open TimbukSolving

let log_src = Logs.Src.create "timbuk.typing.regular"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type TYPED_PATTERN = TypedPattern.S
module type SOLVER = Solver.S

type 'partition abs_partition =
  | Known of 'partition
  | Unknown

type ('ty, 'partition) abs_type = ('partition abs_partition) * 'ty

type ('q, 'partition) solved_state =
  | Old of 'q
  | New of 'partition abs_partition * 'q * int

module type S = sig
  module Location : sig type t end

  module TypeSystem : RefinedTypeSystem.S
  module TypeAut = TypeSystem.TypeAut

  module TypedPattern : TypedPattern.S with type Sym.t = TypeAut.Sym.t and type Type.t = TypeAut.State.t * Location.t
  module TypedTrs : Relation.S with type ord = TypedPattern.t and type elt = TypedPattern.t * TypedPattern.t

  module RegularType : TypedTerm.TYPE with type t = TypeAut.StateSet.t
  module RegularTypePartition : Set.S with type elt = RegularType.t

  module RegularTypedPattern : TYPED_PATTERN with type Sym.t = TypeAut.Sym.t and type Var.t = TypedPattern.Var.t and type Type.t = RegularType.t * Location.t

  type error =
    | BiTypedTerm of (TypeAut.Sym.t Term.term * TypeAut.State.t * TypeAut.State.t * RegularTypePartition.t)

  exception Error of error

  type t

  val values_abstraction : t -> TypeAut.t

  val abstraction : t -> TypeAut.t

  val type_pattern : RegularTypePartition.t -> ?forbid:TypeAut.StateSet.t -> TypedPattern.t -> t -> RegularTypedPattern.t list * t
end

module TypedPatternBuilder = TypedPattern

module Make
    (Location : sig type t end)
    (TypeSystem : RefinedTypeSystem.S)
    (TypedPattern : TypedPattern.S with type Sym.t = TypeSystem.TypeAut.Sym.t and type Type.t = TypeSystem.TypeAut.State.t * Location.t)
    (TypedTrs : Relation.S with type ord = TypedPattern.t and type elt = TypedPattern.t * TypedPattern.t)
    (Solver : SOLVER with type Var.t = TypeSystem.TypeAut.State.t)
    (MinimalSolver : SOLVER with type Var.t = int)
= struct
  module Location = Location

  module TypeSystem = TypeSystem
  module TypeAut = TypeSystem.TypeAut
  module TypedPattern = TypedPattern
  module TypedTrs = TypedTrs

  module Sym = TypeAut.Sym
  module Var = TypedPattern.Var
  module Type = TypeAut.State

  let type_of (_, (ty, _)) = ty

  module RegularType = struct
    type t = TypeAut.StateSet.t

    let choose =
      TypeAut.StateSet.choose

    let mem =
      TypeAut.StateSet.mem

    let compare =
      TypeAut.StateSet.compare

    let equal =
      TypeAut.StateSet.equal

    let hash =
      Hashtbl.hash

    let product a b =
      let c = TypeAut.StateSet.product Type.product a b in
      if TypeAut.StateSet.is_empty c then
        None
      else
        Some c

    let print t fmt =
      let elts = TypeAut.StateSet.elements t in
      Format.fprintf fmt "{%t}" (List.print Type.print "," elts)
  end

  module LocRegularType = LocType.Make (Location) (RegularType)

  module RegularTypePartition = Set.Make (RegularType)

  module RegularTypedTerm = TypedTerm.Make (Sym) (LocRegularType)
  module RegularTypedPattern = TypedPatternBuilder.Make (Sym) (Var) (LocRegularType)

  let print_abs_partition v fmt =
    match v with
    | Known partition ->
      let elts = RegularTypePartition.elements partition in
      Format.fprintf fmt "%t" (List.print RegularType.print "|" elts)
    | Unknown ->
      Format.fprintf fmt "abs"

  module AbsType = struct
    type t = (Type.t, RegularTypePartition.t) abs_type

    let compare_values a b =
      match a, b with
      | Known a, Known b ->
        RegularTypePartition.compare a b
      | Known _, _ ->
        1
      | _, Known _ ->
        -1
      | Unknown, Unknown ->
        0

    let compare (a, qa) (b, qb) =
      let c = Type.compare qa qb in
      if c = 0 then compare_values a b else c

    let value_equal a b =
      match a, b with
      | Known a, Known b ->
        RegularTypePartition.equal a b
      | Unknown, Unknown ->
        true
      | _, _ -> false

    let equal (a, qa) (b, qb) =
      Type.equal qa qb && value_equal a b

    let hash =
      Hashtbl.hash

    let value_product a b =
      match a, b with
      | Known a, Known b ->
        begin
          match RegularTypePartition.product RegularType.product a b with
          | c when RegularTypePartition.is_empty c -> None
          | c -> Some (Known c)
        end
      | Unknown, Known _ ->
        Some Unknown
      | Known _, Unknown ->
        Some Unknown
      | Unknown, Unknown ->
        Some Unknown

    let product (a, qa) (b, qb) =
      if Type.equal qa qb then
        match value_product a b with
        | Some v -> Some (v, qa)
        | None -> None
      else
        None

    let print (v, q) fmt =
      Format.fprintf fmt "<%t:%t>" (print_abs_partition v) (Type.print q)
  end

  module LocAbsType = LocType.Make (Location) (AbsType)

  module SolvedType = struct
    type t = (Type.t, RegularTypePartition.t) solved_state

    let compare_abs_partition a b =
      match a, b with
      | Known pa, Known pb ->
        RegularTypePartition.compare pa pb
      | Known _, Unknown -> 1
      | _, Known _ -> -1
      | Unknown, Unknown -> 0

    let equal_abs_partition a b =
      match a, b with
      | Known pa, Known pb ->
        RegularTypePartition.equal pa pb
      | Unknown, Unknown -> true
      | _ -> false

    let compare a b =
      match a, b with
      | Old a, Old b ->
        Type.compare a b
      | Old _, _ -> 1
      | _, Old _ -> -1
      | New (pa, qa, a), New (pb, qb, b) ->
        let c = a - b in
        if c = 0 then
          let c = Type.compare qa qb in
          if c = 0 then compare_abs_partition pa pb
          else c
        else c

    let equal a b =
      match a, b with
      | Old a, Old b ->
        Type.equal a b
      | New (pa, qa, a), New (pb, qb, b) ->
        a = b && Type.equal qa qb && equal_abs_partition pa pb
      | _ -> false

    let product a b =
      if equal a b then Some a else None

    let hash = Hashtbl.hash

    let print t fmt =
      match t with
      | Old q -> Type.print q fmt
      | New (p, q, i) ->
        Format.fprintf fmt "%d@<%t:%t>" i (print_abs_partition p) (Type.print q)
  end

  module LocSolvedType = LocType.Make (Location) (SolvedType)

  type lhs_signature = TypeAut.Sym.t * Type.t list * Type.t

  module TypedLHS = struct
    type t = lhs_signature * RegularTypePartition.t

    let compare ((fa, la, qa), tya) ((fb, lb, qb), tyb) =
      let c = TypeAut.Sym.compare fa fb in
      if c = 0 then
        let c = Type.compare qa qb in
        if c = 0 then
          let c = List.compare Type.compare la lb in
          if c = 0 then RegularTypePartition.compare tya tyb
          else c
        else c
      else c

    (* let equal ((fa, la, qa), tya) ((fb, lb, qb), tyb) =
       TypeAut.Sym.equal fa fb &&
       Type.equal qa qb &&
       List.for_all2 (fun ta tb -> Type.equal ta tb) la lb &&
       RegularTypePartition.equal tya tyb

       let hash =
       Hashtbl.hash

       let product a b =
       None *)

    let print ((f, l, ty), tys) fmt =
      let types = RegularTypePartition.elements tys in
      Format.fprintf fmt "%t(%t):%t:%t"
        (TypeAut.Sym.print f)
        (List.print Type.print ", " l)
        (List.print RegularType.print "|" types)
        (Type.print ty)
  end

  module FlatTypedLHS = struct
    type t = lhs_signature * TypeSystem.TypeSet.t

    let compare ((fa, la, qa), tya) ((fb, lb, qb), tyb) =
      let c = TypeAut.Sym.compare fa fb in
      if c = 0 then
        let c = Type.compare qa qb in
        if c = 0 then
          let c = List.compare Type.compare la lb in
          if c = 0 then TypeSystem.TypeSet.compare tya tyb
          else c
        else c
      else c

    (* let equal ((fa, la, qa), tya) ((fb, lb, qb), tyb) =
       TypeAut.Sym.equal fa fb &&
       Type.equal qa qb &&
       List.for_all2 (fun ta tb -> Type.equal ta tb) la lb &&
       RegularTypePartition.equal tya tyb

       let hash =
       Hashtbl.hash

       let product a b =
       None *)

    let print ((f, l, ty), tys) fmt =
      Format.fprintf fmt "%t(%t):{%t}:%t"
        (TypeAut.Sym.print f)
        (List.print Type.print ", " l)
        (TypeSystem.TypeSet.print Type.print "," tys)
        (Type.print ty)
  end

  module SolvedAut = Automaton.Make (Sym) (SolvedType) (NoLabel)
  module SolvedTypedPattern = TypedPatternBuilder.Make (Sym) (Var) (LocSolvedType)
  module TypeAut2Solved = Automaton.Ext (TypeAut) (SolvedAut)
  module Solved2TypeAut = Automaton.Ext (SolvedAut) (TypeAut)

  (* module AbsTypedTerm = TypedTerm.Make (Sym) (AbsType) *)
  module AbsTypedPattern = TypedPatternBuilder.Make (Sym) (Var) (LocAbsType)
  module AbsTypedRule = Rule.Make (AbsTypedPattern)
  module AbsTypedTrs = Relation.Make (AbsTypedPattern) (AbsTypedRule)

  module Factorizer = Factorizer.Make (TypeAut) (RegularTypePartition) (Solver)

  type status =
    | Fixpoint
    | Computed of RegularTypePartition.t list

  module LHSMap = Map.Make (TypedLHS)
  module FlatLHSMap = Map.Make (FlatTypedLHS)

  type fixpoint_learner = TypeSystem.t -> AbsTypedTrs.t -> SolvedAut.t option

  type error =
    | BiTypedTerm of (TypeAut.Sym.t Term.term * TypeAut.State.t * TypeAut.State.t * RegularTypePartition.t)

  exception Error of error

  type t = {
    trs: TypedTrs.t;
    (** Considered TRS. *)

    type_system: TypeSystem.t;
    (** The refined type system. *)

    lhs_map: status LHSMap.t;
    (** Mapping from function call + expected output partition to required input partitions.
        If the computation is still running, a Fixpoint value is associated to the key so that
        recursive functions are detected. *)

    flat_lhs_map: TypeAut.t FlatLHSMap.t;

    find_fixpoint: fixpoint_learner;
    (** [find_fixpoint type_knowledge refined_type_system abs_aut abs_typed_trs]
        must find a valid solution automaton to the input abs-typed TRS fragment,
        that is, produce a well-typed automaton resolving every unknown type in the input TRS *)

    refiner: Type.t -> Type.t
    (** Refine a base type into a new fresh (sub)type. *)
  }

  let create trs type_system fixpoint_learner refiner =
    {
      trs = trs;
      type_system = type_system;
      lhs_map = LHSMap.empty;
      flat_lhs_map = FlatLHSMap.empty;
      find_fixpoint = fixpoint_learner;
      refiner = refiner
    }

  (** Find all the rules applicable to a given symbol signature in the considered TRS. *)
  let applicable_rules (f, sub_tys, ty) t =
    TypedTrs.filter (
      fun (lhs, _) ->
        match lhs with
        | TypedPattern.Cons (f', l'), (ty', _) when Sym.equal f f' && Type.equal ty ty' ->
          let sub_tys' = List.map type_of l' in
          List.for_all2 Type.equal sub_tys sub_tys'
        | _ -> false
    ) t.trs

  (** Decorate the given pattern with abs-types so that the whole pattern has the given abs-type.
      All the sub-patterns abs-types are [Unknown] in the output pattern. *)
  let rec abs_type_pattern_unknown abs_ty = function
    | TypedPattern.Cons (f, l), (_, span) ->
      let typed_l = List.map (function p -> abs_type_pattern_unknown (Unknown, type_of p) p) l in
      AbsTypedPattern.Cons (f, typed_l), (abs_ty, span)
    | TypedPattern.Var x, (_, span) ->
      AbsTypedPattern.Var x, (abs_ty, span)
    | TypedPattern.Cast _, _ ->
      raise (Invalid_argument "1 cast patterns not handled.")

  let flatten_partition partition =
    RegularTypePartition.fold (
      fun states flat_partition ->
        TypeAut.StateSet.fold (
          fun refined_ty flat_partition ->
            TypeSystem.TypeSet.add refined_ty flat_partition
        ) states flat_partition
    ) partition TypeSystem.TypeSet.empty

  let map_partition map partition =
    RegularTypePartition.fold (
      fun states mapped_partition ->
        let mapped_states = TypeAut.StateSet.fold (
            fun q mapped_states ->
              match map q with
              | Some mapped_q -> TypeAut.StateSet.add mapped_q mapped_states
              | None -> mapped_states
          ) states TypeAut.StateSet.empty
        in
        if TypeAut.StateSet.is_empty mapped_states then
          mapped_partition
        else
          RegularTypePartition.add mapped_states mapped_partition
    ) partition RegularTypePartition.empty

  let subtype_partition (partition, simple_ty) sub_ty t =
    let map, type_system = TypeSystem.subtype_partition t.type_system (flatten_partition partition, simple_ty) sub_ty in
    map_partition map partition, { t with type_system = type_system }

  let subtype_abs_type abs_type sub_ty t =
    match abs_type with
    | Unknown, simple_ty -> (Unknown, sub_ty), t
    | Known partition, simple_ty ->
      let new_partition, t = subtype_partition (partition, simple_ty) sub_ty t in
      (Known new_partition, sub_ty), t

  (** Compute the intersection of two abs-types.
      The two abs-types must be partitions of the same type or it will raise an Invalid_argument exception. *)
  let abs_type_intersection (abs_partition1, ty1) (abs_partition2, ty2) t =
    let simple_ty = TypeSystem.most_precise_type t.type_system ty1 ty2 in
    match abs_partition1, abs_partition2 with
    | Unknown, _ -> (Unknown, simple_ty), t
    | _, Unknown -> (Unknown, simple_ty), t
    | Known partition1, Known partition2 ->
      let partition1, t = subtype_partition (partition1, ty1) simple_ty t in
      let partition2, t = subtype_partition (partition2, ty2) simple_ty t in
      if RegularTypePartition.equal partition1 partition2 then
        (Known partition1, simple_ty), t
      else
        begin
          let states1 = RegularTypePartition.fold TypeAut.StateSet.union partition1 TypeAut.StateSet.empty in
          let states2 = RegularTypePartition.fold TypeAut.StateSet.union partition2 TypeAut.StateSet.empty in
          (* let aut1 = TypeAut.sub_automaton states1 (TypeSystem.refined_automaton t.type_system) in
             let aut2 = TypeAut.sub_automaton states2 (TypeSystem.refined_automaton t.type_system) in
             let aut = TypeAut.merge aut1 aut2 in *)
          let prod, prod_states, type_system = TypeSystem.partition_intersection simple_ty states1 states2 t.type_system in
          let t = { t with type_system = type_system } in
          let module Type2 = Automaton.MakeStateProduct (TypeAut.State) (TypeAut.State) in
          let module UnionFind = UnionFind.Make (Type2) (TypeAut.StateSet) in
          let equiv partition a b =
            RegularTypePartition.exists (
              function states ->
                TypeAut.StateSet.mem a states && TypeAut.StateSet.mem b states
            ) partition
          in
          let uf = UnionFind.create () in
          let default prod_q = TypeAut.StateSet.singleton (prod prod_q) in
          let uf = List.fold_right (
              fun (a, b) uf ->
                List.fold_right (
                  fun (a', b') uf ->
                    if equiv partition1 a a' && equiv partition2 b b' then
                      UnionFind.union ~default (a, b) (a', b') uf
                    else
                      uf
                ) prod_states uf
            ) prod_states uf
          in
          let partition = List.fold_right (
              fun (a, b) partition ->
                let states = UnionFind.find ~default (a, b) uf in
                RegularTypePartition.add states partition
            ) prod_states RegularTypePartition.empty
          in
          (Known partition, simple_ty), t
        end

  let find_super_type t sub_ty partition =
    (* Log.debug (fun m -> m "finding super type of %t in {%t}" (Type.print sub_ty) (RegularTypePartition.print (TypeAut.StateSet.print Type.print ", ") "; " partition)); *)
    let exception Found of TypeAut.State.t in
    try
      RegularTypePartition.iter (
        function states ->
          TypeAut.StateSet.iter (
            function ty ->
              if TypeSystem.is_subtype t.type_system ty sub_ty then begin
                raise (Found ty)
              end;
          ) states
      ) partition;
      failwith "No valid super type"
    with
    | Found ty -> ty

  (** For a given state-substitution and a given pattern,
      Find the refined type (a state) of the pattern.
      The input substitution must give, for each variable,
      a refined type (a state) that is inside its abs-partition. *)
  let refined_type_of (t : t) (sigma :  AbsTypedPattern.Var.t -> TypeAut.State.t * TypeAut.State.t) abs_typed_pattern : (TypeAut.State.t * TypeAut.State.t) option =
    let exception Found of (TypeAut.State.t * TypeAut.State.t) in
    let rec iter_refined_types g : AbsTypedPattern.t -> unit = function
      | AbsTypedPattern.Var x, ((Known partition, simple_ty), _) ->
        let ty = find_super_type t (fst (sigma x)) partition in
        g (ty, simple_ty)
      | AbsTypedPattern.Cons (f, l), ((Known partition, simple_ty), _) ->
        let rec iter_refined_sub_types g sub_types : AbsTypedPattern.t list -> unit = function
          | [] ->
            g (List.rev sub_types)
          | sub::l ->
            iter_refined_types (function qpair -> iter_refined_sub_types g (qpair::sub_types) l) sub
        in
        iter_refined_sub_types (
          function l_types ->
            let conf = TypeAut.Configuration.Cons (f, List.map (function (q, _) -> TypeAut.Configuration.of_var q) l_types) in
            let states = TypeAut.states_for_configuration conf (TypeSystem.refined_knowledge_automaton t.type_system) in
            TypeAut.LabeledStateSet.iter (
              function (q, _) ->
                if RegularTypePartition.exists (function set -> TypeAut.StateSet.mem q set) partition then
                  g (q, simple_ty)
            ) states
        ) [] l
      | AbsTypedPattern.Cast abs_typed_pattern, ((Known partition, simple_ty), _) ->
        iter_refined_types (
          function (sub_ty, _) ->
            RegularTypePartition.iter (
              function states ->
                TypeAut.StateSet.iter (
                  function ty ->
                    if TypeSystem.is_subtype t.type_system ty sub_ty then
                      g (ty, simple_ty)
                ) states
            ) partition
        ) abs_typed_pattern
      | _, _ ->
        raise (Invalid_argument "Unknown partition")
    in
    try
      iter_refined_types (
        function qpair -> raise (Found qpair)
      ) abs_typed_pattern;
      None
    with
    | Found qpair -> Some qpair

  exception Found_renaming of Type.t SolvedAut.StateMap.t

  (** Find a renaming between new and old states in a SolvedAut given a type-system automaton. *)
  let find_renaming solved_aut type_system =
    let id_renaming : Type.t SolvedAut.StateMap.t = SolvedAut.fold_states (
        fun solved_q renaming ->
          match solved_q with
          | Old q -> SolvedAut.StateMap.add solved_q q renaming
          | New _ -> renaming
      ) solved_aut SolvedAut.StateMap.empty
    in
    SolvedAut.fold_states (
      fun solved_q renaming ->
        match solved_q with
        | Old _ -> renaming
        | New _ ->
          begin
            try
              TypeAut.fold_states (
                fun q () ->
                  (* Log.debug (fun m -> m "Comparing states %t and %t@." (SolvedAut.State.print solved_q) (TypeAut.State.print q)); *)
                  let label_eq _ _ = true in
                  match TypeAut2Solved.state_renaming ~epsilon:false ~knowledge:renaming label_eq type_system solved_aut q solved_q with
                  | Some renaming ->
                    (* Log.debug (fun m -> m "Renaming found@."); *)
                    raise (Found_renaming renaming)
                  | None -> ()
              ) type_system ();
              renaming
            with
            | Found_renaming renaming -> renaming
          end
    ) solved_aut id_renaming

  (** For a given abs-typed pattern, return the variable substitution that best fit the constraints given by the pattern.
      In details: the input rec-typed pattern is not linear. Some variables may be refined-typed differently in different positions.
      So a single variable has possibly multiple types. We want a substitution that gives only one type per variable,
      which still satisfy the needed abstraction.
      It may generate new abstractions on the way, by refining existing ones.  *)
  (*  Because of subtyping, a single variable may also have multiple simple-types, so the refined-types of a variable may
      be incompatible. *)
  let most_precise_substitution abs_typed_pattern simple_sigma t =
    (* debug "MGS: %t@." (AbsTypedPattern.print abs_typed_pattern); *)
    let rec find_most_precise_substitution (sigma, t) = function
      | AbsTypedPattern.Cons (_, l), _ ->
        List.fold_left find_most_precise_substitution (sigma, t) l
      | AbsTypedPattern.Var x, (abs_ty, _) ->
        begin
          match AbsTypedPattern.Substitution.find_opt x sigma with
          | Some abs_ty' ->
            let new_abs_ty, t = abs_type_intersection abs_ty abs_ty' t in
            AbsTypedPattern.Substitution.add x new_abs_ty sigma, t
          | None ->
            let sub_ty = simple_sigma x in
            let new_abs_ty, t = subtype_abs_type abs_ty sub_ty t in
            AbsTypedPattern.Substitution.add x new_abs_ty sigma, t
        end
      | AbsTypedPattern.Cast pattern, _ ->
        find_most_precise_substitution (sigma, t) pattern
    in
    find_most_precise_substitution (AbsTypedPattern.Substitution.empty, t) abs_typed_pattern

  let minimalise solved_aut =
    (* debug "TO MINIMALIZE:\n%t\n@." (SolvedAut.print solved_aut); *)
    (* Log.debug (fun m -> m "minimalizing\n%t" (SolvedAut.print solved_aut)); *)
    let smt_value = function
      | Old _ ->
        failwith "NOOOO!"
      | New (_, _, id) ->
        MinimalSolver.Variable id
    in
    let try_compare a b =
      match a, b with
      | New (_, tya, _), New (_, tyb, _) when not (Type.equal tya tyb) ->
        Some (Type.compare tya tyb)
      | New (_, _, ia), New (_, _, ib) when ia = ib ->
        Some 0
      | Old tya, Old tyb ->
        Some (Type.compare tya tyb)
      | Old _, New _ ->
        Some 1
      | New _, Old _ ->
        Some (-1)
      | _ ->
        None
    in
    let declare q solver =
      match q with
      | New (_, _, id) -> MinimalSolver.declare id solver
      | _ -> solver
    in
    let solver = SolvedAut.fold_transition_pairs (
        fun conf _ q conf' _ q' solver ->
          let solver = declare q (declare q' solver) in
          let exception Ignore in
          begin match conf, conf' with
            | SolvedAut.Configuration.Cons (f, l), SolvedAut.Configuration.Cons (f', l') when SolvedAut.Sym.equal f f' ->
              let l = List.map SolvedAut.Configuration.normalized l in
              let make_neq_disjunction n n' disjunction =
                match try_compare n n' with
                | None ->
                  let clause = (MinimalSolver.Neq (smt_value n, smt_value n')) in
                  clause::disjunction
                | Some 0 -> disjunction
                | Some _ -> raise Ignore
              in
              begin try
                  begin match try_compare q q' with
                    | Some 0 ->
                      solver
                    | Some _ ->
                      (* debug "CONJUCTION DIF FROM %t -> %t and %t -> %t\n@." (Aut.Configuration.print conf) (Node.print node) (Aut.Configuration.print conf') (Node.print node'); *)
                      (* Nodes are differents for sure. *)
                      (* Then configurations [conf] and [conf'] must be differents for
                         the resulting automaton to be deterministic. *)
                      (* We first reduce the sub-nodes... *)
                      let l' = List.map SolvedAut.Configuration.normalized l' in
                      (* ...and then create the disequalities disjunction. *)
                      let disjunction = List.fold_right2 make_neq_disjunction l l' [] in
                      MinimalSolver.add (MinimalSolver.Or disjunction) solver
                    | None ->
                      (* debug "CONJUCTION FROM %t -> %t and %t -> %t\n@." (Aut.Configuration.print conf) (Node.print node) (Aut.Configuration.print conf') (Node.print node'); *)
                      (* We don't know yet if the nodes are equals. *)
                      (* Then configurations [conf] and [conf'] must be differents if [node] and [node'] are. *)
                      (* We first reduce the sub-nodes... *)
                      let l' = List.map SolvedAut.Configuration.normalized l' in
                      (* ...and then create the disequalities disjunction. *)
                      let disjunction = List.fold_right2 make_neq_disjunction l l' [] in
                      (* To that, we add that the two nodes can be equals. *)
                      let disjunction = (MinimalSolver.Eq (smt_value q, smt_value q'))::disjunction in
                      (* debug "\nDIFFERENCIATE %t and %t\n@." (Node.print node) (Node.print node'); *)
                      MinimalSolver.add (MinimalSolver.Or disjunction) solver
                  end
                with
                | Ignore ->
                  (* Log.debug (fun m -> m "ignoring %t and %t" (SolvedAut.Configuration.print conf) (SolvedAut.Configuration.print conf')); *)
                  solver
              end
            | _ -> solver
          end
      ) solved_aut (MinimalSolver.create ())
    in
    (* Log.debug (fun m -> m "solver\n%t" (MinimalSolver.print solver)); *)
    (* let print_model m fmt =
       MinimalSolver.Model.iter (fun key value ->
          Format.fprintf fmt "%d -> %d@." key value
        ) m
       in *)
    match MinimalSolver.solve solver with
    | MinimalSolver.Sat model ->
      (* Log.debug (fun m -> m "model\n%t" (print_model model)); *)
      let map_label l = l in
      let map_state = function
        | New (abs_partition, simple_ty, i) ->
          New (abs_partition, simple_ty, MinimalSolver.Model.find i model)
        | q -> q
      in
      let minimalized = SolvedAut.map map_label map_state solved_aut in
      (* Log.debug (fun m -> m "minimalized\n%t" (SolvedAut.print minimalized)); *)
      minimalized
    | _ -> failwith "Unable to minimalize (unsat/unknown result)."

  let expected_sub_partitions_from_solved_aut type_system solved_aut lhs_sig expected_partition =
    begin match Factorizer.factorize lhs_sig expected_partition (TypeSystem.is_direct_subtype type_system) solved_aut with
      | Some expected_sub_partitions ->
        (* **************************************************************** *)
        (* let too_large p =
           Factorizer.Partition.cardinal p >= 6
           in
           if List.exists too_large expected_sub_partitions then begin
           Log.err (fun m -> m "\nPROBLEM HERE for %t:\n%@." (TypedLHS.print (lhs_sig, expected_partition)));
           let print_partition p fmt =
            let print_set s fmt =
              Format.fprintf fmt "{%t}" (TypeAut.StateSet.print TypeAut.State.print "|" s)
            in
            Format.fprintf fmt "[%t]" (Factorizer.Partition.print print_set "," p)
           in
           Log.err (fun m -> m "expected sub partitions: %t@." (List.print print_partition "; " expected_sub_partitions));
           failwith "stop."
           end; *)
        (* **************************************************************** *)
        expected_sub_partitions
      | None ->
        RegularTypePartition.fold_pairs (
           fun states states' () ->
            TypeAut.StateSet.fold_pairs2 (
              fun q q' () ->
                let qs = TypeAut.StateSet.add q' (TypeAut.StateSet.singleton q) in
                match TypeAut.pick_term_in_intersection_opt qs (TypeSystem.refined_knowledge_automaton type_system) with
                | Some term -> raise (Error (BiTypedTerm (term, q, q', expected_partition)))
                | None -> ()
            ) states states' ()
           ) expected_partition ();
        Log.err (fun m -> m "\nINVALID SOLUTION for %t:\n%t\n@." (TypedLHS.print (lhs_sig, expected_partition)) (TypeAut.print solved_aut));
        (* expected_partition *)
        failwith "typing/src/regular.ml: produced automaton is not a valid solution, but no counter example was found. This is a bug."
    end

  let is_functional t f =
    let aut = TypeSystem.automaton t.type_system in
    let exception Found in
    let _ = 0 in
    try
      TypeAut.fold_transitions (
        fun conf () _ () ->
          match conf with
          | TypeAut.Configuration.Cons (f', _) when Sym.equal f f' ->
            raise Found
          | _ -> ()
      ) aut ();
      true
    with
    | Found -> false

  let rec expected_sub_abs_tys cons_sig expected_partition t =
    let (_f, sub_tys, _ty) = cons_sig in
    begin match Factorizer.factorize cons_sig expected_partition (TypeSystem.is_subtype t.type_system) (TypeSystem.refined_automaton t.type_system) with (* TODO *)
      | Some expected_sub_partitions ->
        (* We already computed what input-partitions are needed to get the expected output partition. *)
        (* For instance, if the considered symbol is a value constructor, then we ends up here. *)
        let expected_sub_abs_tys = List.map2 (fun sub_partition sub_ty -> Known sub_partition, sub_ty) expected_sub_partitions sub_tys in
        expected_sub_abs_tys, t
      | None ->
        (* Log.debug (fun m -> m "not a constructor symbol w.r.t\n%t" (TypeSystem.TypeAut.print (TypeSystem.refined_automaton t.type_system))); *)
        (* This is not a constructor symbol. There must be some rule to apply then. *)
        (* We need to find those rules in order to know what sub-types are excpected. *)
        expected_lhs_sub_abs_tys cons_sig expected_partition t
    end

  and expected_lhs_sub_abs_tys lhs_sig expected_partition t =
    let (_f, sub_tys, _ty) = lhs_sig in
    let lhs_map_key = (lhs_sig, expected_partition) in
    begin match LHSMap.find_opt lhs_map_key t.lhs_map with
      | Some Fixpoint ->
        (* We are currently analysing the function. It is a recursive function. *)
        (* For now, we give Unknown sub partitions.
           The parent call will detect it and call the fixpoint solver. *)
        let expected_sub_abs_tys = List.map (function ty -> Unknown, ty) sub_tys in
        expected_sub_abs_tys, t
      | Some (Computed expected_sub_partitions) ->
        (* We already have analysed the function for this given expected output partition. *)
        let expected_sub_abs_tys = List.map2 (fun sub_partition sub_ty -> Known sub_partition, sub_ty) expected_sub_partitions sub_tys in
        expected_sub_abs_tys, t
      | None ->
        (* We never tried to analize this function for this given expected output partition. *)
        (* First, we put the Fixpoint value in the lhs-map to detect eventual fixpoints. *)
        let t =
          {
            t with
            lhs_map = LHSMap.add lhs_map_key Fixpoint t.lhs_map
          }
        in
        (* The we resolve the function. *)
        let expected_sub_partitions, t = resolve_function lhs_sig expected_partition t in
        (* Finaly we save what we found so we never compute it again. *)
        let t =
          {
            t with
            lhs_map = LHSMap.add lhs_map_key (Computed expected_sub_partitions) t.lhs_map;
          }
        in
        (* **************************************************************** *)
        (* Log.debug (fun m -> m "\nSOLUTION for %t:" (TypedLHS.print (lhs_sig, expected_partition)));
           let print_partition p fmt =
           let print_set s fmt =
            Format.fprintf fmt "{%t}" (TypeAut.StateSet.print TypeAut.State.print "|" s)
           in
           Format.fprintf fmt "[%t]" (Factorizer.Partition.print print_set "," p)
           in
           Log.debug (fun m -> m "expected sub partitions: %t@." (List.print print_partition ", " expected_sub_partitions)); *)
        (* **************************************************************** *)
        (* debug "\nNEW REFINED TYPE-SYSTEM:\n%t\n@." (TypeAut.print (TypeSystem.refined_automaton t.type_system));
           debug "\nNEW TYPE-KNOWLEDGE:\n%t\n@." (TypeAut.print (TypeSystem.refined_knowledge_automaton t.type_system)); *)
        let expected_sub_abs_tys = List.map2 (fun sub_partition sub_ty -> Known sub_partition, sub_ty) expected_sub_partitions sub_tys in
        expected_sub_abs_tys, t
    end

  (** Actually find the expected input partitions for a given function call and expected output partition.
      It is assumed that [lsh_sig] is not a value constructor symbol. *)
  and resolve_function lhs_sig expected_partition t =
    let flat_lhs_key = (lhs_sig, flatten_partition expected_partition) in
    let f, sub_tys, ty = lhs_sig in
    begin match FlatLHSMap.find_opt flat_lhs_key t.flat_lhs_map with
      | Some solved_aut ->
        let expected_sub_partitions = expected_sub_partitions_from_solved_aut t.type_system solved_aut lhs_sig expected_partition in
        expected_sub_partitions, t
      | None ->
        let expected_abs_ty = Known expected_partition, ty in
        (* First we get the set of applicable TRS rules on this signed symbol. *)
        let applicable_rules = applicable_rules lhs_sig t in
        (* Then we try to type every right-hand-side of the rules with the expected partition. *)
        (* What we get is [semi_typed_applicable_rules], a list of each rule with the rhs abs-typed,
           and a abs-type substitution giving the type of each variable in the rhs. *)
        let semi_typed_applicable_rules, t = TypedTrs.fold
            (
              fun (lhs, rhs) (semi_typed_applicable_rules, t) ->
                let abs_typed_rhs, t = abs_type_pattern expected_abs_ty rhs t in
                (* Log.debug (fun m -> m "LHS: %t" (AbsTypedPattern.print abs_typed_rhs)); *)
                let semi_typed_rule = (lhs, abs_typed_rhs) in
                (semi_typed_rule::semi_typed_applicable_rules, t)
            )
            applicable_rules
            ([], t)
        in
        (* If some applicable rule rhs abs-types are still [Unknown], it means the
           function is recursive. *)
        (* This function will help us detect this case. *)
        let is_recursive (_, abs_typed_rhs) =
          let is_unknown = function
            | (Unknown, _) -> true
            | _ -> false
          in
          let rec has_unknown_partition = function
            | AbsTypedPattern.Cons (_, l), (abs_ty, _) ->
              is_unknown abs_ty || List.exists has_unknown_partition l
            | AbsTypedPattern.Var _, (abs_ty, _) ->
              is_unknown abs_ty
            | AbsTypedPattern.Cast pattern, (abs_ty, _) ->
              is_unknown abs_ty || has_unknown_partition pattern
          in
          has_unknown_partition abs_typed_rhs
        in
        (* Now we can test for recursivity. We just check is there exists a rule typed with [Unknown]. *)
        (* We have two different ways of finding the input partitions whether it is recursive or not. *)
        (* In both cases, we get ... *)
        let refined_type_knowledge_fragment, t = if List.exists is_recursive semi_typed_applicable_rules then
            (* If it is recursive, we need to learn the invariant. *)
            resolve_recursive_function lhs_sig semi_typed_applicable_rules expected_partition t
          else begin
            (* If it is not recursive, we still have some work to do to extract the input partitions. *)
            Log.debug (fun m -> m "Applicable rules: %t" (TypedTrs.print applicable_rules));
            resolve_non_recursive_function lhs_sig semi_typed_applicable_rules expected_partition t
          end
        in
        (* Extract the found abstractions. *)
        let abstractions = SolvedAut.fold_states (
            fun q abstractions ->
              match q with
              | New (Unknown, ty, id) ->
                Log.debug (fun m -> m "Add %t in the abstraction of %t" (SolvedAut.State.print q) (TypeAut.State.print ty));
                let abstraction = match TypeAut.StateMap.find_opt ty abstractions with
                  | Some abstraction ->
                    SolvedAut.StateSet.add q abstraction
                  | None -> SolvedAut.StateSet.singleton q
                in
                TypeAut.StateMap.add ty abstraction abstractions
              | _ -> abstractions
          ) refined_type_knowledge_fragment TypeAut.StateMap.empty
        in
        (* Now we want to eliminate new states that are equivalent to (a renaming of) old states. *)
        (* However in this case we want to ignore non-constructor symbols. *)
        (* So first we construct a constructor-only (or value only) version of [refined_type_knowledge_fragment]. *)
        let refined_type_system_fragment = SolvedAut.filter (
            fun conf _ _ ->
              match conf with
              | SolvedAut.Configuration.Cons (f', _) ->
                (* We eliminate non-constructors symbols. *)
                not (is_functional t f')
              | _ -> true
          ) refined_type_knowledge_fragment
        in
        let map_data _ = () in
        let map_label _ = () in
        let map_state q = Old q in
        let refined_type_system = TypeAut2Solved.map map_data map_label map_state (TypeSystem.automaton t.type_system) in
        let refined_type_system = SolvedAut.merge refined_type_system_fragment refined_type_system in
        let refined_type_system = SolvedAut.reduce refined_type_system in
        (* Now we can find a renaming with the old states... *)
        let renaming = find_renaming refined_type_system (TypeSystem.refined_automaton t.type_system) in
        (* ...and use this renaming to replace new states with there renamed old counterparts. *)
        let rename_state solved_q =
          match SolvedAut.StateMap.find_opt solved_q renaming with
          | Some q -> Old q
          | None -> solved_q
        in
        let id x = x in
        let solved_aut = SolvedAut.map id rename_state refined_type_knowledge_fragment in
        (* The produced solution probably have new states. *)
        (* In this step we actually create the new states. *)
        let partitions = Hashtbl.create 8 in
        let add_to_partition ty refined_ty =
          match Hashtbl.find_opt partitions ty with
          | Some partition ->
            Hashtbl.replace partitions ty (TypeSystem.TypeSet.add refined_ty partition)
          | None ->
            Hashtbl.add partitions ty (TypeSystem.TypeSet.singleton refined_ty)
        in
        let new_states = Hashtbl.create 8 in
        let id x = x in
        let map_state = function
          | Old old_q -> old_q
          | New (_, ty, id) ->
            begin
              match Hashtbl.find_opt new_states (ty, id) with
              | Some new_q -> new_q
              | None ->
                let new_q = t.refiner ty in
                Hashtbl.add new_states (ty, id) new_q;
                add_to_partition ty new_q;
                new_q
            end
        in
        let rec map_conf = function
          | SolvedAut.Configuration.Cons (f, l) ->
            TypeAut.Configuration.Cons (f, List.map map_conf l)
          | SolvedAut.Configuration.Var solved_q ->
            TypeAut.Configuration.Var (map_state solved_q)
        in
        let map_rename_states solved_states =
          SolvedAut.StateSet.fold (
            fun q states ->
              TypeAut.StateSet.add (map_state (rename_state q)) states
          ) solved_states TypeAut.StateSet.empty
        in
        (* let solved_types = Aut.StateMap.map (SolvedAut.StateSet.map map_state) solved_types in *)
        let refined_type_system, type_knowledge, type_system = SolvedAut.fold_transitions (
            fun conf () q (refined_type_system, type_knowledge, type_system) ->
              match conf with
              | SolvedAut.Configuration.Var q' ->
                refined_type_system, type_knowledge, TypeSystem.declare_subtype (map_state q) (map_state q') type_system
              | _ ->
                let refined_type_system = match q with
                  | New _ ->
                    TypeAut.add_transition (map_conf conf) () (map_state q) refined_type_system
                  | _ -> refined_type_system
                in
                let type_knowledge = TypeAut.add_transition (map_conf conf) () (map_state q) type_knowledge in
                refined_type_system, type_knowledge, type_system
          ) solved_aut (TypeSystem.refined_automaton t.type_system, TypeSystem.refined_knowledge_automaton t.type_system, t.type_system)
        in
        let remove_epsilon conf _ _ =
          match conf with
          | SolvedAut.Configuration.Var _ -> false
          | _ -> true
        in
        let solved_aut = Solved2TypeAut.map ~filter:remove_epsilon id id map_state solved_aut in
        let type_system = TypeSystem.update refined_type_system type_knowledge type_system in

        let type_system = TypeAut.StateMap.fold (
            fun ty abstraction type_system ->
              TypeSystem.declare_partition ty (map_rename_states abstraction) type_system
          ) abstractions type_system
        in
        (* Log.debug (fun m -> m "Partitions declared (A).@."); *)
        Log.debug (fun m -> m "Final solution:\n%t@." (TypeAut.print solved_aut));
        let expected_sub_partitions = expected_sub_partitions_from_solved_aut type_system solved_aut lhs_sig expected_partition in
        let type_system = List.fold_left2 (
            fun type_system simple_ty partition ->
              TypeSystem.declare_partition simple_ty (flatten_partition partition) type_system
          ) type_system sub_tys expected_sub_partitions
        in
        (* Log.debug (fun m -> m "Partitions declared (B).@."); *)
        let t =
          { t with
            flat_lhs_map = FlatLHSMap.add flat_lhs_key solved_aut t.flat_lhs_map;
            type_system = type_system
          }
        in
        expected_sub_partitions, t
    end

  and extract_abs_typed_trs t (lhs, abs_typed_rhs) abs_typed_trs =
    (* debug "EXTRACT from %t -> %t@." (TypedPattern.print lhs) (AbsTypedPattern.print abs_typed_rhs); *)
    let abs_ty = type_of abs_typed_rhs in
    let abs_typed_lhs = abs_type_pattern_unknown abs_ty lhs in
    let abs_rule = (abs_typed_lhs, abs_typed_rhs) in
    if not (AbsTypedTrs.mem abs_rule abs_typed_trs) then begin
      let abs_typed_trs = AbsTypedTrs.add abs_rule abs_typed_trs in
      (* If we never visited this rule, then we need to follow it. *)
      (* For each sub-pattern typed with an unknown partition, we need to add *)
      (* its applicable rewriting rules. *)
      let is_unresolved l expected_abs_ty =
        let is_unresolved_abs_type = function
          | Unknown, _ -> true
          | _ -> false
        in
        is_unresolved_abs_type expected_abs_ty || List.exists (function p -> is_unresolved_abs_type (type_of p)) l
      in
      AbsTypedPattern.fold (
        fun abs_typed_pattern abs_typed_trs ->
          begin match abs_typed_pattern with
            | AbsTypedPattern.Cons (f, l), (expected_abs_ty, _) when is_unresolved l expected_abs_ty ->
              let ty = snd expected_abs_ty in
              let sub_tys = List.map (function p -> snd (type_of p)) l in
              let cons_sig = (f, sub_tys, ty) in
              let applicable_rules = applicable_rules cons_sig t in
              TypedTrs.fold (
                fun (lhs, rhs) abs_typed_trs ->
                  let (abs_typed_rhs : AbsTypedPattern.t), t = abs_type_pattern expected_abs_ty rhs t in
                  let semi_typed_rule = (lhs, abs_typed_rhs) in
                  extract_abs_typed_trs t semi_typed_rule abs_typed_trs
              ) applicable_rules abs_typed_trs
            | _ ->
              (* We ignore everything that is not an applicable pattern with *)
              (* unknown partition type. *)
              abs_typed_trs
          end
      ) abs_typed_rhs abs_typed_trs
    end else begin
      (* If the rule is already known, then we don't need to follow it. *)
      abs_typed_trs
    end

  and resolve_recursive_function lhs_sig semi_typed_applicable_rules expected_partition t =
    Log.info (fun m -> m "Solving recursive function: %t" (TypedLHS.print (lhs_sig, expected_partition)));
    (* We want to extract the fragment of TRS that we need to resolve the fixpoint. *)
    let abs_typed_trs = List.fold_right (extract_abs_typed_trs t) semi_typed_applicable_rules AbsTypedTrs.empty in
    (* Finaly, we use the user-given fixpoint finder to find the correct solved-automaton. *)
    begin match t.find_fixpoint t.type_system abs_typed_trs with
      | Some solved_aut -> solved_aut, t
      | None ->
        raise (Invalid_argument "Cannot find fixpoint classes for this function.")
    end

  and resolve_non_recursive_function lhs_sig semi_typed_applicable_rules expected_partition t =
    Log.info (fun m -> m "Solving non recursive function: %t" (TypedLHS.print (lhs_sig, expected_partition)));
    (* debug "Function is not recursive. Direct resolution.@."; *)
    (* A little function to spawn new ids. *)
    let id_count = ref 0 in
    let next_id () =
      let id = !id_count in
      id_count := id + 1;
      id
    in
    (* Add the corresponding abs-type substitution for each semi-typed rule. *)
    let semi_typed_applicable_rules, t = List.fold_right (
        fun (lhs, abs_typed_rhs) (semi_typed_applicable_rules, t) ->
          let simple_sigma = TypedPattern.substitution lhs in
          let simple_sigma x = fst (TypedPattern.Substitution.find x simple_sigma) in
          (* To be able to type [lhs], we need to find how each variable has been typed in [abs_typed_rhs]. *)
          (* However, since [rhs] is not linear, we may have a variable with multiple types. *)
          (* We use [most_precise_substitution] to find the most precise required type for each variable. *)
          let substitution, t = most_precise_substitution abs_typed_rhs simple_sigma t in
          ((lhs, abs_typed_rhs, substitution)::semi_typed_applicable_rules, t)
      ) semi_typed_applicable_rules ([], t)
    in
    (* We have the abs-type of every right-hand-side. *)
    (* A abs-type is partition of a type, where each partition element is a set of states composing the partition. *)
    (* We want to reason on the state level and give, for each possible variable-to-state substititon in the *)
    (* input pattern, the corresponding state in the abs-type. *)
    (* The following function will help us visit every possible variable-to-state substititon given an *)
    (* abs-type substititon. *)
    let fold_state_substitutions f substitution acc =
      let bindings = AbsTypedPattern.Substitution.bindings substitution in
      let rec fold_combinations sigma bindings acc =
        match bindings with
        | [] ->
          f sigma acc
        | (x, ty)::bindings' ->
          begin
            match ty with
            | Unknown, _ -> failwith "Unknown type partition in a non-recursive function. This is a bug."
            | Known partition, simple_ty ->
              RegularTypePartition.fold (
                fun states acc ->
                  TypeAut.StateSet.fold (
                    fun q acc ->
                      let sigma' y = if Var.equal x y then q, simple_ty else sigma y in
                      fold_combinations sigma' bindings' acc
                  ) states acc
              ) partition acc
          end
      in
      fold_combinations (fun _ -> raise Not_found) bindings acc
    in
    (* Compute the list of all [semi_typed_applicable_rules] but with state substitutions. *)
    let state_typed_applicable_rules = List.fold_right (
        fun (lhs, abs_typed_rhs, substitution) state_typed_applicable_rules ->
          fold_state_substitutions (
            fun state_substitution state_typed_applicable_rules ->
              (* debug "STATE-TYPED lhs: %t@." (SolvedTypedPattern.print lhs); *)
              (lhs, abs_typed_rhs, state_substitution)::state_typed_applicable_rules
          ) substitution state_typed_applicable_rules
      ) semi_typed_applicable_rules []
    in

    (* (* We extract the states on which the pattern depends on. *)
       let states_dependencies = List.fold_right (
        fun (pattern, _, sigma) states_dependencies ->
          TypedPattern.fold (
            fun pattern states_dependencies ->
              (* debug "fold %t@." (TypedPattern.print pattern); *)
              match pattern with
              | TypedPattern.Var x, ty ->
                let q = try fst (sigma x) with Not_found -> ty in
                TypeAut.StateSet.add q states_dependencies
              | _ -> states_dependencies
          ) pattern states_dependencies
       ) state_typed_applicable_rules TypeAut.StateSet.empty
       in
       (* Extract the type-system fragment we will be using. *)
       let refined_type_knowledge_fragment = TypeAut.sub_automaton states_dependencies (TypeSystem.refined_automaton t.type_system) in
       (* Later we will have to differenciate the new introduced states from the old ones. *) *)

    let table = Hashtbl.create 8 in
    let old_state_as_new simple_ty q =
      match Hashtbl.find_opt table (q, simple_ty) with
      | Some solved_q -> solved_q
      | None ->
        (* let ty = TypeSystem.simple_type_of_refined t.type_system q in *)
        let solved_q = New (Unknown, simple_ty, next_id ()) in
        (* Log.debug (fun m -> m "new state dep %t:%t -> %t" (Type.print q) (Type.print simple_ty) (SolvedAut.State.print solved_q)); *)
        Hashtbl.add table (q, simple_ty) solved_q;
        solved_q
    in

    (* let refined_type_knowledge_fragment = SolvedAut.empty in *)
    (* Each sub-pattern of the left-hand-side of each applicable rule will be typed with a new state. *)
    (* The following function do that. The new states and configurations will be added in the input type-system automaton. *)
    let newtype_pattern sigma pattern (q, simple_ty) refined_type_knowledge_fragment : SolvedTypedPattern.t * SolvedAut.t =
      let rec newtype_sub_pattern pattern refined_type_knowledge_fragment =
        match pattern with
        | TypedPattern.Var x, (ty, span) ->
          let solved_q = try
              let q, _ = sigma x in
              old_state_as_new ty q
            with
            | Not_found -> old_state_as_new ty ty
          in
          (SolvedTypedPattern.Var x, (solved_q, span)), refined_type_knowledge_fragment
        | TypedPattern.Cons (f, l), (ty, span) ->
          let typed_l, refined_type_knowledge_fragment = List.fold_right (
              fun pattern (typed_l, refined_type_knowledge_fragment)  ->
                let typed_pattern, refined_type_knowledge_fragment = newtype_sub_pattern pattern refined_type_knowledge_fragment in
                typed_pattern :: typed_l, refined_type_knowledge_fragment
            ) l ([], refined_type_knowledge_fragment)
          in
          let l_types = List.map type_of typed_l in
          let new_q = New (Unknown, ty, next_id ()) in
          let conf = SolvedAut.Configuration.Cons (f, List.map SolvedAut.Configuration.of_var l_types) in
          let refined_type_knowledge_fragment = SolvedAut.add_transition conf () new_q refined_type_knowledge_fragment in
          (SolvedTypedPattern.Cons (f, typed_l), (new_q, span)), refined_type_knowledge_fragment
        | TypedPattern.Cast _, _ ->
          raise (Invalid_argument "5 cast patterns not handled.")
      in
      match pattern with
      | TypedPattern.Var x, (_, span) ->
        (SolvedTypedPattern.Var x, (Old q, span)), refined_type_knowledge_fragment
      | TypedPattern.Cons (f, l), (_, span) ->
        let typed_l, refined_type_knowledge_fragment = List.fold_right (
            fun pattern (typed_l, refined_type_knowledge_fragment)  ->
              let typed_pattern, refined_type_knowledge_fragment = newtype_sub_pattern pattern refined_type_knowledge_fragment in
              typed_pattern :: typed_l, refined_type_knowledge_fragment
          ) l ([], refined_type_knowledge_fragment)
        in
        let l_types = List.map type_of typed_l in
        let solved_q = Old q in
        let conf = SolvedAut.Configuration.Cons (f, List.map SolvedAut.Configuration.of_var l_types) in
        let refined_type_knowledge_fragment = SolvedAut.add_transition conf () solved_q refined_type_knowledge_fragment in
        (SolvedTypedPattern.Cons (f, typed_l), (solved_q, span)), refined_type_knowledge_fragment
      | TypedPattern.Cast _, _ ->
        raise (Invalid_argument "6 cast patterns not handled.")
    in
    (* State-type each lhs of the applicable rules. *)
    let _solved_typed_lhss, refined_type_knowledge_fragment = List.fold_right (
        fun (lhs, abs_typed_rhs, sigma) (solved_typed_lhss, refined_type_knowledge_fragment) ->
          match refined_type_of t sigma abs_typed_rhs with
          | Some (q, simple_ty) ->
            let solved_typed_lhs, refined_type_knowledge_fragment = newtype_pattern sigma lhs (q, simple_ty) refined_type_knowledge_fragment in
            (* Log.debug (fun m -> m "lhs: %t@." (SolvedTypedPattern.print solved_typed_lhs)); *)
            solved_typed_lhs::solved_typed_lhss, refined_type_knowledge_fragment
          | None ->
            Format.eprintf "Type knowledge:\n%t@." (TypeAut.print (TypeSystem.refined_knowledge_automaton t.type_system));
            Format.eprintf "UNRESOLVED RHS: %t@." (AbsTypedPattern.print abs_typed_rhs);
            AbsTypedPattern.iter (
              function
              | (AbsTypedPattern.Var x, _) ->
                Format.eprintf "%t <- %t:%t@." (AbsTypedPattern.Var.print x) (Type.print (fst (sigma x))) (Type.print (snd (sigma x)))
              | _ -> ()
            ) abs_typed_rhs;
            failwith "typing/src/regular.ml: unresolved RHS. This is a bug."
      ) state_typed_applicable_rules ([], SolvedAut.empty)
    in

    (* We use the SolvedType and SolvedAut structs for that. *)
    (* let refined_type_knowledge_fragment = TypeAut2Solved.map (function () -> ()) (function x -> x) old_state_as_new refined_type_knowledge_fragment in *)
    (* Log.debug (fun m -> m "Starting with\n%t@." (SolvedAut.print refined_type_knowledge_fragment)); *)

    let type_aut = TypeSystem.refined_automaton t.type_system in
    (* Log.debug (fun m -> m "Type aut\n%t@." (TypeAut.print type_aut)); *)

    let visited = Hashtbl.create 8 in
    let rec add_dependency q simple_ty refined_type_knowledge_fragment =
      match Hashtbl.find_opt visited (q, simple_ty) with
      | Some _ -> refined_type_knowledge_fragment
      | None ->
        begin
          Hashtbl.add visited (q, simple_ty) ();
          let solved_q = old_state_as_new simple_ty q in
          (* Log.debug (fun m -> m "add dep %t:%t -> %t" (Type.print q) (Type.print simple_ty) (SolvedAut.State.print solved_q)); *)
          let confs = TypeAut.configurations_for_state q type_aut in
          let simple_confs = TypeAut.configurations_for_state simple_ty type_aut in
          TypeAut.LabeledConfigurationSet.fold2 (
            fun (conf, _) (simple_conf, _) refined_type_knowledge_fragment ->
              match conf, simple_conf with
              | TypeAut.Configuration.Cons (f, l), TypeAut.Configuration.Cons (f', sl) when TypeAut.Sym.equal f f' ->
                let l = List.map TypeAut.Configuration.normalized l in
                let sl = List.map TypeAut.Configuration.normalized sl in
                (* Log.debug (fun m -> m "common conf %t / %t" (TypeAut.Configuration.print conf) (TypeAut.Configuration.print simple_conf)); *)
                if List.for_all2 (TypeSystem.is_subtype t.type_system) sl l then begin (* FIXME is_subtype? *)
                  (* Log.debug (fun m -> m "accepted"); *)
                  let solved_l = List.map2 old_state_as_new sl l in
                  let solved_conf = TypeAut.Configuration.Cons (f, List.map SolvedAut.Configuration.of_var solved_l) in
                  let refined_type_knowledge_fragment = SolvedAut.add_transition solved_conf () solved_q refined_type_knowledge_fragment in
                  List.fold_right2 add_dependency l sl refined_type_knowledge_fragment
                end else begin
                  (* Log.debug (fun m -> m "rejected"); *)
                  refined_type_knowledge_fragment
                end
              | _ ->
                refined_type_knowledge_fragment
          ) confs simple_confs refined_type_knowledge_fragment
        end
    in

    let refined_type_knowledge_fragment = Hashtbl.fold (
        fun (q, simple_ty) _ refined_type_knowledge_fragment ->
          add_dependency q simple_ty refined_type_knowledge_fragment
      ) table refined_type_knowledge_fragment
    in

    (* debug "solved aut:\n%t@." (SolvedAut.print refined_type_knowledge_fragment); *)
    (* We have found state for each lhs. We now need to determinize it. *)
    (* The [state_of_class] will create a state for each classes of states during the determinization. *)
    let state_of_class k _simple_ty =
      (* debug "map %t@." (PPrint.print_ext_set (module SolvedAut.StateSet) SolvedAut.State.print "," k); *)
      if SolvedAut.StateSet.cardinal k = 1 then
        (* If the state is alone in its class, its easy, we just need to reuse it. *)
        SolvedAut.StateSet.choose k
      else
        (* If it is not alone... *)
        let is_representant = function
          | New _ -> true
          | Old q ->
            let confs = TypeAut.configurations_for_state q (TypeSystem.automaton t.type_system) in
            TypeAut.LabeledConfigurationSet.cardinal confs > 0
        in
        try let ty = match SolvedAut.StateSet.search is_representant k with
            | New (_, ty, _) -> ty
            | Old ty -> ty
          in
          New (Unknown, ty, next_id ())
        with
        | Not_found ->
          Log.err (fun m -> m "No type found in %t@." (SolvedAut.StateSet.print SolvedAut.State.print "," k));
          Log.info (fun m -> m "This is most likely due to an invalid target partition");
          raise Not_found
    in
    (* Log.debug (fun m -> m "\nRAW:\n%t\n@." (SolvedAut.print refined_type_knowledge_fragment)); *)
    (* Log.debug (fun m -> m "determinising:\n%t@." (SolvedAut.print refined_type_knowledge_fragment)); *)
    (* let init_classes = TypeAut.StateSet.fold (fun q set -> SolvedAut.StateSet.add (Old q) set) states_dependencies SolvedAut.StateSet.empty in *)

    let type_of = function
      | New (_, ty, _) -> ty
      | Old ty -> ty
    in
    let refined_type_knowledge_fragment = SolvedAut.determinise_typed (module Type) type_of state_of_class refined_type_knowledge_fragment in
    (* Log.debug (fun m -> m "\nDETERMINIZED:\n%t\n@." (SolvedAut.print refined_type_knowledge_fragment)); *)

    (* let refined_type_knowledge_fragment = SolvedAut.merge refined_type_knowledge_fragment type_knowledge_fragment in *)
    (* Minimalization *)
    (* Now it is normalized, but it may not be minimal. *)
    (* However we don't want to mangle new and old states together. *)
    (* So we will use the ~filter parameter of [minimalise] to ignore old states. *)
    (* let new_states_only q q' =
       match q, q' with
       | New _, New _ -> true
       | _ -> false
       in
       let refined_type_knowledge_fragment = SolvedAut.minimalise ~filter:new_states_only refined_type_knowledge_fragment in *)
    let refined_type_knowledge_fragment = minimalise refined_type_knowledge_fragment in
    (* Log.debug (fun m -> m "\nMINIMALIZED:\n%t\n@." (SolvedAut.print refined_type_knowledge_fragment)); *)
    (* debug "solved aut:\n%t@." (SolvedAut.print refined_type_knowledge_fragment); *)
    refined_type_knowledge_fragment, t

  and abs_type_pattern expected_abs_ty pattern t : AbsTypedPattern.t * t =
    (* Log.debug (fun m -> m "type: %t with %t@." (TypedPattern.print pattern) (AbsType.print expected_abs_ty)); *)
    begin match pattern with
      | TypedPattern.Var x, (_, span) ->
        (* nothing to really do here. *)
        let abs_ty = expected_abs_ty in
        let abs_typed_pattern = AbsTypedPattern.Var x, (abs_ty, span) in
        abs_typed_pattern, t
      | TypedPattern.Cons (f, l), (ty, span) ->
        let sub_tys = List.map type_of l in
        begin match expected_abs_ty with
          | Known expected_partition, _ ->
            let cons_sig = (f, sub_tys, ty) in
            (* Get the expected partitions for the sub patterns. *)
            let expected_sub_abs_tys, t = expected_sub_abs_tys cons_sig expected_partition t in
            (* debug "EXPECT %t@." (PPrint.print_list AbsType.print ", " expected_sub_abs_tys); *)
            (* Try to type every sub pattern with the expected partition. *)
            let abs_typed_l, t = List.fold_right2 (
                fun expected_sub_abs_ty sub_pattern (l, t) ->
                  let abs_typed_sub_pattern, t = abs_type_pattern expected_sub_abs_ty sub_pattern t in
                  (abs_typed_sub_pattern::l, t)
              ) expected_sub_abs_tys l ([], t)
            in
            (* Build the final abs-typed pattern. *)
            let abs_ty = Known expected_partition, ty in
            let abs_typed_pattern = AbsTypedPattern.Cons (f, abs_typed_l), (abs_ty, span) in
            (* debug "RESULT abs-typed pattern: %t@." (AbsTypedPattern.print abs_typed_pattern); *)
            abs_typed_pattern, t
          | Unknown, _ ->
            (* Try to type every sub pattern with the expected partition. *)
            let abs_typed_l, t = List.fold_right (
                fun sub_pattern (l, t) ->
                  let sub_ty = type_of sub_pattern in
                  let expected_abs_sub_ty = (Unknown, sub_ty) in
                  let abs_typed_sub_pattern, t = abs_type_pattern expected_abs_sub_ty sub_pattern t in
                  (abs_typed_sub_pattern::l, t)
              ) l ([], t)
            in
            (* Build the final abs-typed pattern. *)
            let abs_ty = Unknown, ty in
            let abs_typed_pattern = AbsTypedPattern.Cons (f, abs_typed_l), (abs_ty, span) in
            (* debug "RESULT abs-typed pattern: %t@." (AbsTypedPattern.print abs_typed_pattern); *)
            abs_typed_pattern, t
        end
      | TypedPattern.Cast (pattern, (sub_ty, span)), _ ->
        begin match expected_abs_ty with
          | Known expected_partition, ty ->
            let subtyped_partition, t = subtype_partition (expected_partition, ty) sub_ty t in
            let abs_typed_pattern, t = abs_type_pattern (Known subtyped_partition, sub_ty) (pattern, (sub_ty, span)) t in
            let abs_ty = Known expected_partition, ty in
            (AbsTypedPattern.Cast abs_typed_pattern, (abs_ty, span)), t
          | Unknown, ty ->
            let abs_typed_pattern, t = abs_type_pattern (Unknown, sub_ty) (pattern, (sub_ty, span)) t in
            let abs_ty = Unknown, ty in
            (AbsTypedPattern.Cast abs_typed_pattern, (abs_ty, span)), t
        end
    end

  let values_abstraction t =
    (TypeSystem.refined_automaton t.type_system)

  let abstraction t =
    (TypeSystem.refined_knowledge_automaton t.type_system)

  let decompose_abs_typed_pattern abs_pattern t =
    (* Log.debug (fun m -> m "decompose: %t@." (AbsTypedPattern.print abs_pattern)); *)
    let fold_abs_type f (abs_partition, _) accu =
      match abs_partition with
      | Known partition ->
        RegularTypePartition.fold f partition accu
      | Unknown -> raise (Invalid_argument "Pattern is abstract")
    in
    let type_knowledge = TypeSystem.refined_knowledge_automaton t.type_system in
    let rec extract_regular_pattern sigma = function
      | AbsTypedPattern.Cons (f, l), ((Known partition, _), span) ->
        let regular_l = List.map (extract_regular_pattern sigma) l in
        let simple_l = List.map (function (_, (reg_ty, _)) -> RegularType.choose reg_ty) regular_l in
        let simple_conf = TypeAut.Configuration.Cons (f, List.map TypeAut.Configuration.of_var simple_l) in

        let simple_tys = TypeAut.states_for_configuration simple_conf type_knowledge in
        let regular_ty = RegularTypePartition.search (function set -> TypeAut.LabeledStateSet.exists (function (ty, _) -> RegularType.mem ty set) simple_tys) partition in

        RegularTypedPattern.Cons (f, regular_l), (regular_ty, span)
      | AbsTypedPattern.Var x, (_, span) ->
        let regular_ty = AbsTypedPattern.Substitution.find x sigma in
        RegularTypedPattern.Var x, (regular_ty, span)
      | _ -> raise (Invalid_argument "Pattern is abstract")
    in
    let sigma = AbsTypedPattern.substitution abs_pattern in
    let sigma = AbsTypedPattern.Substitution.map (fun (abs_ty, _) -> abs_ty) sigma in
    AbsTypedPattern.Substitution.fold_combinations (
      fun sigma regular_patterns ->
        let regular_pattern = extract_regular_pattern sigma abs_pattern in
        regular_pattern::regular_patterns
    ) sigma fold_abs_type []

  let type_pattern expected_partition ?(forbid=TypeAut.StateSet.empty) pattern t =
    let ty = type_of pattern in
    let expected_abs_ty = (Known expected_partition, ty) in
    let abs_type_pattern, t = abs_type_pattern expected_abs_ty pattern t in
    let regular_patterns = decompose_abs_typed_pattern abs_type_pattern t in
    regular_patterns, t
end
