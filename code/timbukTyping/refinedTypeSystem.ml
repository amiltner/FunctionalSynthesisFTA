open Collections
open Timbuk

let log_src = Logs.Src.create "timbuk.typing.refinedTypeSystem"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type S = sig
  (* module Type : Automaton.STATE *)
  module TypeAut : Automaton.S with type Label.t = unit and type data = unit
  module TypeSet : Set.S with type t = TypeAut.StateSet.t and type elt = TypeAut.StateSet.elt
  module TypeSetSet : Set.S with type elt = TypeSet.t

  type t

  val create : TypeAut.t -> TypeAut.t -> (unit -> TypeAut.State.t) -> t
  val automaton : t -> TypeAut.t
  val refined_automaton : t -> TypeAut.t
  val refined_knowledge_automaton : t -> TypeAut.t
  val update : TypeAut.t -> TypeAut.t -> t -> t
  (* val simple_types_of_refined : t -> TypeAut.State.t -> TypeAut.StateSet.t *)
  (* val has_simple_type : t -> TypeAut.State.t -> TypeAut.State.t -> bool *)
  val complements_of : t -> TypeAut.State.t -> TypeSetSet.t
  val declare_partition : TypeAut.State.t -> TypeSet.t -> t -> t
  val declare_subtype : TypeAut.State.t -> TypeAut.State.t -> t -> t
  val is_subtype : t -> TypeAut.State.t -> TypeAut.State.t -> bool
  val is_direct_subtype : t -> TypeAut.State.t -> TypeAut.State.t -> bool
  val most_precise_type : t -> TypeAut.State.t -> TypeAut.State.t -> TypeAut.State.t
  val subtype_partition : t -> TypeSet.t * TypeAut.State.t -> TypeAut.State.t -> (TypeAut.State.t -> TypeAut.State.t option) * t
  type type_product = TypeAut.State.t * TypeAut.State.t -> TypeAut.State.t
  val partition_intersection : TypeAut.State.t -> TypeSet.t -> TypeSet.t -> t -> type_product * (TypeAut.State.t * TypeAut.State.t) list * t
end

module Make (TypeAut : Automaton.S with type Label.t = unit and type data = unit) = struct
  module TypeAut = TypeAut
  module Type = TypeAut.State
  module TypeSet = TypeAut.StateSet
  module TypeSetSet = Set.Make (TypeSet)

  module TypeMap = HashTable.Make (Type)

  type type_product = TypeAut.State.t * TypeAut.State.t -> TypeAut.State.t

  type t = {
    simple_type_system: TypeAut.t;
    (** Initial type system without refinement. *)

    refined_type_system: TypeAut.t;
    (** Refined type system. *)

    refined_type_knowledge: TypeAut.t;
    (** Refined type system with function types. *)

    (* simple_types: TypeSet.t TypeMap.t; *)
    (** Refined types associated simple types. *)

    complements: TypeSetSet.t TypeMap.t;
    (** Refined types complements. *)

    super_types: TypeSet.t TypeMap.t;
    (** Associate the supertype of each type if any. *)

    state_factory: unit -> Type.t;

    partition_subtyping_table: ((TypeAut.State.t * TypeAut.State.t * TypeSet.t), (TypeAut.State.t -> TypeAut.State.t option)) Hashtbl.t;

    partitions_intersection_table: ((TypeAut.State.t * TypeSet.t * TypeSet.t), (type_product * (TypeAut.State.t * TypeAut.State.t) list)) Hashtbl.t
  }

  let automaton t = t.simple_type_system

  let refined_automaton t = t.refined_type_system

  let refined_knowledge_automaton t = t.refined_type_knowledge

  let update refined_types refined_knowledge t =
    {
      t with
      refined_type_system = refined_types;
      refined_type_knowledge = refined_knowledge
    }

  (* let simple_types_of_refined t refined_ty =
    begin match TypeMap.find_opt refined_ty t.simple_types with
      | Some simple_tys -> simple_tys
      | None ->
        let msg = Format.asprintf "Unknown refined type `%t`. Use [declare_partition] to declare the refined type with the partition it is in." (Type.print refined_ty) in
        raise (Invalid_argument msg)
    end *)

  (* let has_simple_type t simple_ty refined_ty =
     begin match TypeMap.find_opt refined_ty t.simple_types with
      | Some simple_tys -> TypeSet.mem simple_ty simple_tys
      | None -> false
     end *)

  let complements_of t refined_ty =
    begin match TypeMap.find_opt refined_ty t.complements with
      | Some complements -> complements
      | None -> TypeSetSet.empty
    end

  let rec is_subtype t simple_ty sub_ty =
    (* Log.debug (fun m -> m "check if %t is a subtype of %t" (Type.print sub_ty) (Type.print simple_ty)); *)
    Type.equal sub_ty simple_ty ||
    match TypeMap.find_opt sub_ty t.super_types with
    | Some super_tys ->
      (* Log.debug (fun m -> m "checking supertypes {%t}" (TypeSet.print Type.print ", " sub_ty) (Type.print ty)); *)
      TypeSet.exists (is_subtype t simple_ty) super_tys
    | None ->
      (* Log.debug (fun m -> m "%t has no super-type" (Type.print sub_ty)); *)
      false

  let rec is_direct_subtype t simple_ty sub_ty =
    (* Log.debug (fun m -> m "check if %t is a subtype of %t" (Type.print sub_ty) (Type.print simple_ty)); *)
    Type.equal sub_ty simple_ty ||
    match TypeMap.find_opt sub_ty t.super_types with
    | Some super_tys ->
      (* Log.debug (fun m -> m "checking supertypes {%t}" (TypeSet.print Type.print ", " sub_ty) (Type.print ty)); *)
      TypeSet.mem simple_ty super_tys
    | None ->
      (* Log.debug (fun m -> m "%t has no super-type" (Type.print sub_ty)); *)
      false

  let declare_subtype ty sub_ty t =
    if Type.equal ty sub_ty then t else begin
      if is_subtype t sub_ty ty then failwith "type recursion detected";
      Log.debug (fun m -> m "declare %t as a subtype of %t" (Type.print sub_ty) (Type.print ty));
      let super_tys = match TypeMap.find_opt sub_ty t.super_types with
        | Some super_tys ->
          TypeSet.add ty super_tys
        | None ->
          TypeSet.singleton ty
      in
      { t with super_types = TypeMap.set sub_ty super_tys t.super_types }
    end

  (* let declare_simple_type simple_ty ty t =
     let t = declare_subtype simple_ty ty t in
     (* Log.debug (fun m -> m "declare %t as a subtype of %t" (Type.print ty) (Type.print simple_ty)); *)
     let simple_tys = match TypeMap.find_opt ty t.simple_types with
      | Some simple_tys -> TypeSet.add simple_ty simple_tys
      | None -> TypeSet.singleton simple_ty
     in
     {
      t with
      simple_types = TypeMap.set ty simple_tys t.simple_types
     } *)

  let declare_complement refined_ty complement t =
    if TypeSet.is_empty complement then t else
      {
        t with
        complements = TypeMap.set refined_ty (TypeSetSet.add complement (complements_of t refined_ty)) t.complements
      }

  let declare_partition ty partition t =
    (* Log.debug (fun m -> m "declare partition {%t} for %t" (TypeAut.StateSet.print TypeAut.State.print ", " partition) (TypeAut.State.print ty)); *)
    TypeSet.fold (
      fun refined_ty t ->
        let t = declare_subtype ty refined_ty t in
        let complement = TypeSet.remove refined_ty partition in
        declare_complement refined_ty complement t
    ) partition t

  let most_precise_type t a b =
    if is_subtype t a b then b else
    if is_subtype t b a then a else
      raise (Invalid_argument "types are incompatibles")

  module ProdType = Automaton.MakeStateProduct (Type) (Type)
  module ProdAut = Automaton.Make (TypeAut.Sym) (ProdType) (NoLabel)
  module Prod = Automaton.Product (TypeAut) (TypeAut) (ProdAut)
  module Type2Prod = Automaton.Ext (TypeAut) (ProdAut)

  let product aut1 aut2 t =
    let prod_aut = Prod.product (fun _ _ -> ()) (fun _ _ -> Some ()) (fun a b -> Some (a, b)) aut1 aut2 in
    let prod_aut = ProdAut.reduce prod_aut in
    (* Log.debug (
       fun m -> m "subtyping partition ({%t}, %t) as %t:\n%t"
          (TypeSet.print Type.print ", " partition)
          (Type.print simple_ty)
          (Type.print sub_ty)
          (ProdAut.print prod_aut)
       ); *)
    (** Find a renaming between product states and refined states. *)
    let exception Found_renaming of Type.t ProdAut.StateMap.t in
    let renaming =
      ProdAut.fold_states (
        fun prod_q renaming ->
          try
            TypeAut.fold_states (
              fun q () ->
                let label_eq _ _ = true in
                match Type2Prod.state_renaming ~knowledge:renaming label_eq t.refined_type_system prod_aut q prod_q with
                | Some renaming ->
                  raise (Found_renaming renaming)
                | None -> ()
            ) t.refined_type_system ();
            renaming
          with
          | Found_renaming renaming -> renaming
      ) prod_aut ProdAut.StateMap.empty
    in
    let table = Hashtbl.create 8 in
    let map_prod_state prod_q =
      match Hashtbl.find_opt table prod_q with
      | Some q -> q
      | None ->
        let q = match ProdAut.StateMap.find_opt prod_q renaming with
          | Some q -> q
          | None ->
            let q = t.state_factory () in
            (* Log.debug (fun m -> m "create state %t from %t and %t" (Type.print q) (Type.print (fst prod_q)) (Type.print (snd prod_q))); *)
            (* let t = declare_subtype (fst prod_q) q t in
               let t = declare_subtype (fst prod_q) q t in *)
            q
            (* failwith "TODO: refinedTypeSystem.ml: create state while intersecting automata" *)
        in
        Hashtbl.add table prod_q q;
        q
    in
    let rec map_conf = function
      | ProdAut.Configuration.Var q -> TypeAut.Configuration.Var (map_prod_state q)
      | ProdAut.Configuration.Cons (f, l) ->
        TypeAut.Configuration.Cons (f, List.map map_conf l)
    in
    let refined_type_system = ProdAut.fold_transitions (
        fun conf _ prod_q refined_type_system ->
          TypeAut.add_transition (map_conf conf) () (map_prod_state prod_q) refined_type_system
      ) prod_aut t.refined_type_system
    in
    let t = { t with refined_type_system = refined_type_system } in
    map_prod_state, prod_aut, t

  let subtype_partition t (partition, simple_ty) sub_ty =
    if Type.equal simple_ty sub_ty then
      (fun q -> Some q), t
    else begin
      match Hashtbl.find_opt t.partition_subtyping_table (simple_ty, sub_ty, partition) with
      | Some map_state -> map_state, t
      | None ->
        let type_aut_fragment = TypeAut.sub_automaton partition t.refined_type_system in
        let sub_ty_aut = TypeAut.sub_automaton (TypeSet.singleton sub_ty) t.simple_type_system in
        let map_prod_state, prod_aut, t = product sub_ty_aut type_aut_fragment t in
        let map_state q =
          let prod_q = (sub_ty, q) in
          if ProdAut.is_state_empty prod_q prod_aut then
            None
          else
            Some (map_prod_state prod_q)
        in
        let new_partition, t = TypeSet.fold (
            fun q (new_partition, t) ->
              match map_state q with
              | Some q' ->
                let t = declare_subtype q q' t in
                (* Log.debug (fun m -> m "declare %t as subtype of %t" (Type.print q') (Type.print q)); *)
                (* let t = declare_subtype sub_ty q' t in *)
                TypeSet.add q' new_partition, t
              | None ->
                new_partition, t
          ) partition (TypeSet.empty, t)
        in
        (* Log.debug (
           fun m -> m "new partition is {%t}:%t"
              (TypeSet.print Type.print ", " new_partition)
              (Type.print sub_ty)
           ); *)
        let t = declare_partition sub_ty new_partition t in
        Hashtbl.add t.partition_subtyping_table (simple_ty, sub_ty, partition) map_state;
        map_state, t
    end

  let partition_intersection simple_ty partition1 partition2 t =
    if TypeSet.equal partition1 partition2 then
      (fun (a, b) -> if Type.equal a b then a else raise (Invalid_argument "not in partition")),
      TypeAut.StateSet.fold (fun q l -> (q, q)::l) partition1 [],
      t
    else begin
      match Hashtbl.find_opt t.partitions_intersection_table (simple_ty, partition1, partition2) with
      | Some (map_prod_state, inter_partition) -> map_prod_state, inter_partition, t
      | None ->
        let aut1 = TypeAut.sub_automaton partition1 (refined_automaton t) in
        let aut2 = TypeAut.sub_automaton partition2 (refined_automaton t) in
        let map_prod_state, prod_aut, t = product aut1 aut2 t in
        let prod_partition = ProdAut.final_states prod_aut in
        let mapped_prod_partition, t = ProdAut.StateSet.fold (
            fun (a, b) (partition, t) ->
              let sub_ty = map_prod_state (a, b) in
              let t = declare_subtype a sub_ty t in
              let t = declare_subtype b sub_ty t in
              (* Log.debug (fun m -> m "declare %t as subtype of %t" (Type.print a) (Type.print sub_ty)); *)
              (* Log.debug (fun m -> m "declare %t as subtype of %t" (Type.print b) (Type.print sub_ty)); *)
              TypeAut.StateSet.add sub_ty partition, t
          ) prod_partition (TypeAut.StateSet.empty, t)
        in
        let t = declare_partition simple_ty mapped_prod_partition t in
        let inter_partition = ProdAut.StateSet.elements prod_partition in
        Hashtbl.add t.partitions_intersection_table (simple_ty, partition1, partition2) (map_prod_state, inter_partition);
        map_prod_state, inter_partition, t
    end

  let create simple_types refined_types state_factory =
    let epsilon_free conf _ _ =
      match conf with
      | TypeAut.Configuration.Cons _ -> true
      | TypeAut.Configuration.Var _ -> false
    in
    let simple_type_system = TypeAut.filter epsilon_free simple_types in
    let refined_type_system = TypeAut.filter epsilon_free refined_types in
    let t = {
      simple_type_system = simple_type_system;
      refined_type_system = refined_type_system;
      refined_type_knowledge = refined_type_system;
      (* simple_types = TypeMap.create 8; *)
      complements = TypeMap.create 8;
      super_types = TypeMap.create 8;
      state_factory = state_factory;
      partition_subtyping_table = Hashtbl.create 8;
      partitions_intersection_table = Hashtbl.create 8
    }
    in
    (* declaring subtypes *)
    let declare_subtypes conf _ q t =
      match conf with
      | TypeAut.Configuration.Cons _ -> t
      | TypeAut.Configuration.Var sub_q ->
        declare_subtype q sub_q t
    in
    let t = TypeAut.fold_transitions declare_subtypes simple_types t in
    (* declaring reflective partitions. *)
    let declare_simple_partition q t =
      declare_partition q (TypeSet.singleton q) t
    in
    TypeAut.fold_states declare_simple_partition simple_types t
end
