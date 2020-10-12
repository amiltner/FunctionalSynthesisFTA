open Collections

module type STATE = Pattern.VARIABLE
module type LABEL = Pattern.VARIABLE
module type TYPE = TypedTerm.TYPE

module type BASE = sig
  module Sym : Symbol.S
  module State : STATE
  module Label : LABEL
  module Configuration : Pattern.S with type Sym.t = Sym.t and type Var.t = State.t
  module LabeledConfiguration : sig
    type t = Configuration.t * Label.t
    val compare : t -> t -> int
    val print : t -> Format.formatter -> unit
  end
  module LabeledState : sig
    type t = State.t * Label.t
    val product : t -> t -> t option
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
    val print : t -> Format.formatter -> unit
  end
  module StateSet : Set.S with type elt = State.t
  module StateMap : Map.S with type key = State.t
  module ConfigurationSet : Set.S with type elt = Configuration.t
  module ConfigurationMap : Map.S with type key = Configuration.t
  module LabeledConfigurationSet : Set.S with type elt = LabeledConfiguration.t
  module LabeledStateSet : Set.S with type elt = LabeledState.t
  type t
  type data
  val create : data -> t
  val data : t -> data
  val clear : t -> t
  val final_states : t -> StateSet.t
  val configurations_for_states : t -> LabeledConfigurationSet.t StateMap.t
  val states_for_configurations : t -> LabeledStateSet.t ConfigurationMap.t
  val state_parents : State.t -> t -> ConfigurationSet.t
  val add_final_state : State.t -> t -> t
  val add_final_states : StateSet.t -> t -> t
  val set_final_states : StateSet.t -> t -> t
  type hook = Configuration.t -> Label.t -> State.t -> unit
  val add_transition : ?hook:hook -> Configuration.t -> Label.t -> State.t -> t -> t
  val add_transition_unchecked : Configuration.t -> Label.t -> State.t -> t -> t
  val remove_transition : Configuration.t -> Label.t -> State.t -> t -> t
end

module type S = sig
  include BASE
  module Binding : sig
    type t = State.t option * Label.t option
    val product : t -> t -> t option
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
    val print : t -> Format.formatter -> unit
  end
  module SymSet : Set.S with type elt = Sym.t
  module BoundTerm : TypedTerm.S with type Sym.t = Sym.t and type Type.t = Binding.t
  module BoundConfiguration : TypedPattern.S with type Sym.t = Sym.t and type Var.t = Var.t and type Type.t = Binding.t
  type transition = Configuration.t * Label.t * State.t
  (* val all: Label.t -> State.t -> Sym.t list -> t *)
  val alphabet: t -> SymSet.t
  val states : t -> StateSet.t
  val is_final : t -> State.t -> bool
  val state_count : t -> int
  val is_state_empty : State.t -> t -> bool
  val configurations_for_state : State.t -> t -> LabeledConfigurationSet.t
  val states_for_configuration : Configuration.t -> t -> LabeledStateSet.t
  val sub_states_of : t -> State.t -> StateSet.t
  val fold_configurations_for_binding : (LabeledConfiguration.t -> State.t -> 'a -> 'a) -> Binding.t -> t -> 'a -> 'a
  val iter_configurations_for_binding : (LabeledConfiguration.t -> State.t -> unit) -> Binding.t -> t -> unit
  val fold_configurations_for_epsilon_state : (Configuration.t -> 'a -> 'a) -> State.t -> t -> 'a -> 'a
  val iter_configurations_for_epsilon_state : (Configuration.t -> unit) -> State.t -> t -> unit
  val fold_epsilon_class : (State.t -> 'a -> 'a) -> State.t -> t -> 'a -> 'a
  val state_transitive_parents : State.t -> t -> ConfigurationSet.t
  val sub_automaton : StateSet.t -> t -> t
  val mem : Configuration.t -> Label.t -> State.t -> t -> bool
  val mem_configuration : Configuration.t -> t -> bool
  val mem_state : State.t -> t -> bool
  val type_term_in : State.t -> Sym.t Term.term -> t -> BoundTerm.t option
  val type_term : Sym.t Term.term -> t -> BoundTerm.t option
  val recognizes_in : State.t -> Sym.t Term.term -> t -> bool
  val recognizes : Sym.t Term.term -> t -> bool
  val recognizes_state_in : State.t -> State.t -> t -> bool
  val pick_binding_inhabitant : ?epsilon:bool -> Binding.t -> t -> BoundTerm.t
  val pick_binding_inhabitant_opt : ?epsilon:bool -> Binding.t -> t -> BoundTerm.t option
  val pick_term : ?smallest:bool -> ?epsilon:bool -> t -> BoundTerm.t
  val pick_term_opt : ?smallest:bool -> ?epsilon:bool -> t -> BoundTerm.t option
  val pick_term_in : ?epsilon:bool -> State.t -> t -> BoundTerm.t
  val pick_term_in_opt : ?epsilon:bool -> State.t -> t -> BoundTerm.t option
  val pick_term_in_intersection : ?epsilon:bool -> StateSet.t -> t -> Sym.t Term.term
  val pick_term_in_intersection_opt : ?epsilon:bool -> StateSet.t -> t -> Sym.t Term.term option
  val map : ?filter:(Configuration.t -> Label.t -> State.t -> t -> bool) -> (Label.t -> Label.t) -> (State.t -> State.t) -> t -> t
  val filter : (Configuration.t -> Label.t -> State.t -> bool) -> t -> t
  val fold_states : (State.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_transitions : (Configuration.t -> Label.t -> State.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_transition_pairs : ?reflexive:bool -> (Configuration.t -> Label.t -> State.t -> Configuration.t -> Label.t -> State.t -> 'a -> 'a) -> t -> 'a -> 'a
  val label : ((State.t -> 'a) -> State.t -> 'a) -> (State.t -> 'a) -> t -> (State.t -> 'a)
  val merge : t -> t -> t
  val inter : ?hook:(t -> State.t -> unit) -> (data -> data -> data) -> t -> t -> t
  val reachable_states : ?epsilon:bool -> t -> StateSet.t
  val reachable_values : t -> BoundTerm.t StateMap.t
  val reduce : ?epsilon:bool -> ?from_finals:bool -> t -> t
  val complete : ?with_states:StateSet.t -> (Configuration.t -> State.t * Label.t) -> Sym.t list -> t -> t
  val complement : t -> t
  val unepsilon : t -> t
  val determinise : ?init_classes:StateSet.t -> (StateSet.t -> State.t) -> t -> t
  val determinise_typed : ?init_classes:StateSet.t -> (module TYPE with type t = 'a) -> (State.t -> 'a) -> (StateSet.t -> 'a -> State.t) -> t -> t
  val minimalise : ?filter:(State.t -> State.t -> bool) -> t -> t
  val prune_useless : t -> t
  type renaming = State.t StateMap.t
  val state_renaming : ?knowledge:renaming -> t -> t -> State.t -> State.t -> State.t StateMap.t option
  type normalizer = Sym.t -> State.t list -> LabeledState.t
  val add_normalized_transition : ?hook:hook -> normalizer -> Configuration.t -> Label.t -> State.t -> t -> t
  val add_normalized_transitions : ?hook:hook -> normalizer -> transition list -> t -> t
  val add_configurations_to : ?normalizer:normalizer -> ?hook:hook -> LabeledConfiguration.t list -> State.t -> t -> t
  val add_configuration : normalizer -> ?hook:hook -> Configuration.t -> t -> BoundConfiguration.t * t
  val add : normalizer -> ?hook:hook -> Configuration.t -> t -> BoundConfiguration.t * t
  val of_term : normalizer -> Sym.t Term.term -> data -> t
  val of_terms : normalizer -> (Sym.t Term.term) list -> data -> t
  val compare : t -> t -> int
  val print : t -> Format.formatter -> unit
  module Patterns (Var : Pattern.VARIABLE) : sig
    type pattern = (Sym.t, Var.t) Pattern.pattern
    val recognizes_pattern : pattern -> t -> bool
    val recognizes_pattern_in : State.t -> pattern -> t -> bool
    val configuration_of_pattern : (Var.t -> State.t) -> pattern -> Configuration.t
  end
  type dynamic_filter =
    | NoFilter
    | Filter of (State.t -> Label.t -> (bool * dynamic_filter))
  module BoundPatterns (Var : Pattern.VARIABLE) : sig
    type bound_pattern = (Sym.t, Var.t, Binding.t) TypedPattern.typed_pattern
    val fold_pattern_instances : ?epsilon_f:((bound_pattern -> bool) option) -> ?filter:dynamic_filter -> (BoundTerm.t -> 'a -> 'a) -> bound_pattern -> t -> 'a -> 'a
    val instanciate_pattern_opt : ?epsilon:bool -> bound_pattern -> t -> BoundTerm.t option
    val recognizes_bound_pattern : ?epsilon:bool -> bound_pattern -> t -> bool
    val recognizes_bound_pattern_in : ?debug:bool -> ?epsilon:bool -> State.t -> bound_pattern -> t -> bool
  end
end

(** Find or creates an element in a Hastbl.
    e is the key. If no element is mapped to e,
    (f e) is mapped to it and retuned. *)
let find_or_create f map e =
  match Hashtbl.find_opt map e with
  | Some x -> x
  | None ->
    let x = f e in
    Hashtbl.add map e x;
    x

module MakeBase (F : Symbol.S) (Q : STATE) (L : LABEL) = struct
  module Sym = F
  module State = Q
  module Label = L

  module Configuration = Pattern.Make (Sym) (State)

  module LabeledConfiguration = struct
    type t = Configuration.t * Label.t

    let compare (a, la) (b, lb) =
      let c = Label.compare la lb in
      if c = 0 then Configuration.compare a b else c

    let print (c, l) out =
      Configuration.print c out;
      Label.print l out
  end

  module LabeledState = struct
    type t = State.t * Label.t

    let product (a, la) (b, lb) =
      match State.product a b, Label.product la lb with
      | Some c, Some lc -> Some (c, lc)
      | _, _ -> None

    let compare (a, _) (b, _) = State.compare a b

    let equal (a, _) (b, _) = State.equal a b

    let hash (q, _) = State.hash q

    let print (q, l) out =
      Label.print l out;
      State.print q out
  end

  module StateSet = Set.Make (State)
  module StateMap = Map.Make (State)

  module ConfigurationSet = Set.Make (Configuration)
  module ConfigurationMap = Map.Make (Configuration)

  module LabeledStateSet = Set.Make (LabeledState)
  module LabeledConfigurationSet = Set.Make (LabeledConfiguration)

  type t = {
    roots : StateSet.t; (* Final states. *)
    state_confs : LabeledConfigurationSet.t StateMap.t; (* Associates to each state the set of configurations leading to it. *)
    conf_states : LabeledStateSet.t ConfigurationMap.t; (* Associates to each configuration the set of states to go to. *)
    state_parents : ConfigurationSet.t StateMap.t (* Associates to each state the set of configurations it appears in. *)
  }

  type data = unit

  let empty = {
    roots = StateSet.empty;
    state_confs = StateMap.empty;
    conf_states = ConfigurationMap.empty;
    state_parents = StateMap.empty
  }

  let create _ = empty

  let data _ = ()

  let clear _ = empty

  let final_states a = a.roots

  let configurations_for_states a =
    a.state_confs

  let states_for_configurations a =
    a.conf_states

  let state_parents q a =
    match StateMap.find_opt q a.state_parents with
    | Some set -> set
    | None -> ConfigurationSet.empty

  let add_final_state q a = {
    a with
    roots = StateSet.add q (a.roots)
  }

  let add_final_states set a = {
    a with
    roots = StateSet.union set (a.roots)
  }

  let set_final_states set a = {
    a with
    roots = set
  }

  type hook = Configuration.t -> Label.t -> State.t -> unit

  let configurations_for_state q a =
    match StateMap.find_opt q a.state_confs with
    | Some set -> set
    | None -> LabeledConfigurationSet.empty

  (*let is_state_empty q a =
    let confs = configurations_for_state q a in
    LabeledConfigurationSet.is_empty confs*)

  let states_for_configuration conf a =
    match ConfigurationMap.find_opt conf a.conf_states with
    | Some set -> set
    | None -> LabeledStateSet.empty

  (*let sub_states_of a q =
    let confs = configurations_for_state q a in
    LabeledConfigurationSet.fold (
      fun (conf, _) sub_states ->
        match conf with
        | Configuration.Var q' ->
          StateSet.add q' sub_states
        | _ -> sub_states
    ) confs StateSet.empty*)

  let add_transition ?hook conf label q a =
    let add_parent_to q parents = StateMap.add q (ConfigurationSet.add conf (state_parents q a)) parents in
    let call_hook conf q =
      match hook with
      | Some h -> h conf label q
      | None -> ()
    in
    let update_conf q conf = function
      | Some _ -> ()
      | None -> call_hook conf q
    in
    {
      a with
      state_confs = StateMap.add q (LabeledConfigurationSet.update (update_conf q conf) (conf, label) (configurations_for_state q a)) a.state_confs;
      conf_states = ConfigurationMap.add conf (LabeledStateSet.add (q, label) (states_for_configuration conf a)) a.conf_states;
      state_parents = Configuration.fold add_parent_to conf a.state_parents
    }

  let add_transition_unchecked conf label q a =
    let add_parent_to q parents = StateMap.add q (ConfigurationSet.add conf (state_parents q a)) parents in
    {
      a with
      state_confs = StateMap.add q (LabeledConfigurationSet.add (conf, label) (configurations_for_state q a)) a.state_confs;
      conf_states = ConfigurationMap.add conf (LabeledStateSet.add (q, label) (states_for_configuration conf a)) a.conf_states;
      state_parents = Configuration.fold add_parent_to conf a.state_parents;
    }

  let remove_transition conf label q a =
    let remove_parent_from q parents = StateMap.add q (ConfigurationSet.remove conf (state_parents q a)) parents in
    {
      a with
      state_confs = StateMap.add q (LabeledConfigurationSet.remove (conf, label) (configurations_for_state q a)) a.state_confs;
      conf_states = ConfigurationMap.add conf (LabeledStateSet.remove (q, label) (states_for_configuration conf a)) a.conf_states;
      state_parents = Configuration.fold remove_parent_from conf a.state_parents;
    }

  (* let merge a b =
     (* It is assumed that states of a and b are disjoin. *)
     let no_collision _ _ _ = failwith "automata are not disjoined." in
     let conf_collision _ qs1 qs2 = Some (LabeledStateSet.union qs1 qs2) in (* TODO handle duplicated labels *)
     let parents_collision _ parents1 parents2 = Some (ConfigurationSet.union parents1 parents2) in
     {
      roots = StateSet.union a.roots b.roots;
      state_confs = StateMap.union (no_collision) a.state_confs b.state_confs;
      conf_states = ConfigurationMap.union (conf_collision) a.conf_states b.conf_states;
      state_parents = StateMap.union (parents_collision) a.state_parents b.state_parents
     } *)

end

module Extend (B: BASE) = struct
  include B

  type transition = Configuration.t * Label.t * State.t

  module Option = struct
    let product f a b =
      match a, b with
      | Some a, Some b ->
        begin match f a b with
          | Some p -> Some (Some p)
          | None -> None
        end
      | None, None -> Some None
      | Some a, _ -> Some (Some a)
      | _, Some b -> Some (Some b)

    let compare f a b =
      match a, b with
      | Some a, Some b -> f a b
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0

    let equal f a b =
      match a, b with
      | Some a, Some b -> f a b
      | None, None -> true
      | _, _ -> false

    let hash f = function
      | Some lq -> f lq
      | None -> 0

    let print f t out =
      match t with
      | Some lq -> f lq out
      | None -> Format.fprintf out "~"
  end

  module Binding = struct
    type t = State.t option * Label.t option

    let product (qa,la) (qb,lb) =
      match Option.product State.product qa qb, Option.product Label.product la lb with
      | Some q, Some l -> Some (q, l)
      | _, _ -> None

    let compare (qa,la) (qb,lb) =
      let c = Option.compare State.compare qa qb in
      if c = 0 then Option.compare Label.compare la lb else c

    let equal (qa,la) (qb,lb) =
      Option.equal State.equal qa qb && Option.equal Label.equal la lb

    let hash ((q, _) : t) = Option.hash State.hash q

    let print (q, l) out =
      Format.fprintf out ":%t:%t" (Option.print State.print q) (Option.print Label.print l)
  end

  module SymSet = Set.Make (Sym)

  module BoundTerm = TypedTerm.Make (Sym) (Binding)
  module BoundConfiguration = TypedPattern.Make (Sym) (Var) (Binding)

  let configurations_for_state q a =
    match StateMap.find_opt q (configurations_for_states a) with
    | Some set -> set
    | None -> LabeledConfigurationSet.empty

  let is_state_empty q a =
    let confs = configurations_for_state q a in
    LabeledConfigurationSet.is_empty confs

  let states_for_configuration conf a =
    match ConfigurationMap.find_opt conf (states_for_configurations a) with
    | Some set -> set
    | None -> LabeledStateSet.empty

  let sub_states_of a q =
    let confs = configurations_for_state q a in
    LabeledConfigurationSet.fold (
      fun (conf, _) sub_states ->
        match conf with
        | Configuration.Var q' ->
          StateSet.add q' sub_states
        | _ -> sub_states
    ) confs StateSet.empty

  let typed_configuration conf =
    let id = ref 0 in
    let next_id () =
      let i = !id in
      id := i+1;
      i
    in
    let rec type_configuration conf =
      match conf with
      | Configuration.Var q -> BoundConfiguration.Var (Var.of_int (next_id ())), (Some q, None)
      | Configuration.Cons (f, l) -> BoundConfiguration.Cons (f, List.map type_configuration l), (None, None)
    in
    type_configuration conf

  let typed_transition conf label q =
    match conf with
    | Configuration.Var _ ->
      BoundConfiguration.Cast (typed_configuration conf), (Some q, Some label)
    | _ ->
      let typed_conf, _ = typed_configuration conf in
      typed_conf, (Some q, Some label)

  let rec untyped_configuration = function
    | BoundConfiguration.Var _, (Some q, _) -> Configuration.Var q
    | BoundConfiguration.Var _, _ -> failwith "Automaton.untyped_configuration: untyped variable"
    | BoundConfiguration.Cast typed_conf, _ -> untyped_configuration typed_conf
    | BoundConfiguration.Cons (f, l), _ -> Configuration.Cons (f, List.map untyped_configuration l)

  (* fold_epsilon_class with a custom table. *)
  let fold_epsilon_class_aux table f q a x =
    let rec fold_state q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        LabeledConfigurationSet.fold fold_conf (configurations_for_state q a) (f q x)
    and fold_conf (conf, _) x =
      match conf with
      | Configuration.Var q' ->
        fold_state q' x
      | _ -> x
    in
    fold_state q x

  let fold_epsilon_class f q a x =
    let table = Hashtbl.create 8 in
    fold_epsilon_class_aux table f q a x

  let state_typecheck q = function
    | None -> true
    | Some q' -> State.equal q q'

  let label_typecheck lbl = function
    | None -> true
    | Some lbl' -> Label.equal lbl lbl'

  (* let typecheck (q, lbl) (q_typ, lbl_typ) =
     state_typecheck q q_typ && label_typecheck lbl lbl_typ *)

  let fold_epsilon_class_type f q q_typ a x =
    let table = Hashtbl.create 8 in
    let fold_q q x =
      if state_typecheck q q_typ then
        fold_epsilon_class_aux table f q a x
      else
        x
    in
    fold_epsilon_class fold_q q a x

  let state_transitive_parents q a =
    let visited = Hashtbl.create 8 in
    let rec fold_state q set =
      match Hashtbl.find_opt visited q with
      | Some () -> set
      | None ->
        Hashtbl.add visited q ();
        let fold_conf conf set =
          match conf with
          | Configuration.Var _ -> fold_state q set
          | _ -> ConfigurationSet.add conf set
        in
        ConfigurationSet.fold fold_conf (state_parents q a) set
    in
    fold_state q ConfigurationSet.empty

  let fold_transitions f a x =
    let fold_state_confs q confs x =
      let fold_labeled_confs (conf, label) = f conf label q in
      LabeledConfigurationSet.fold (fold_labeled_confs) confs x
    in
    StateMap.fold (fold_state_confs) (configurations_for_states a) x

  let fold_transition_pairs ?(reflexive=false) f t x =
    StateMap.fold_pairs (
      fun q confs q' confs' x ->
        if State.equal q q' then
          begin
            LabeledConfigurationSet.fold_pairs ~reflexive (
              fun (conf, label) (conf', label') x ->
                f conf label q conf' label' q' x
            ) confs x
          end
        else
          begin
            LabeledConfigurationSet.fold (
              fun (conf, label) x ->
                LabeledConfigurationSet.fold (
                  fun (conf', label') x ->
                    f conf label q conf' label' q' x
                ) confs' x
            ) confs x
          end
    ) ~reflexive:true (configurations_for_states t) x

  let fold_states f a x =
    let table = Hashtbl.create 8 in
    let uniq_f q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        f q x
    in
    let rec fold_state q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        LabeledConfigurationSet.fold (fold_labeled_configuration) (configurations_for_state q a) (f q x)
    and fold_labeled_configuration (conf, _) =
      fold_configuration conf
    and fold_configuration conf x =
      match conf with
      | Configuration.Cons (_, l) -> List.fold_right (fold_configuration) l x
      | Configuration.Var q -> fold_state q x
    and fold_transition conf _ q x =
      fold_configuration conf (uniq_f q x)
    in
    let x = StateSet.fold (uniq_f) (final_states a) x in
    fold_transitions (fold_transition) a x

  let states a =
    fold_states (StateSet.add) a (StateSet.empty)

  let is_final a q =
    StateSet.mem q (final_states a)

  let state_count a =
    fold_states (fun _ k -> k + 1) a 0

  let mem conf label state a =
    let states = states_for_configuration conf a in
    LabeledStateSet.mem (state, label) states

  let mem_configuration conf a =
    ConfigurationMap.mem conf (states_for_configurations a)

  let mem_state q a =
    StateMap.mem q (configurations_for_states a) || StateSet.mem q (final_states a)

  let rec fold_configurations_for_binding func ty t x =
    match ty with
    | (Some q, label) ->
      let confs = configurations_for_state q t in
      let label_eq label' =
        match label with
        | Some label -> Label.equal label label'
        | None -> true
      in
      let foreach_conf (conf, label') x =
        if label_eq label' then
          func (conf, label') q x
        else
          x
      in
      LabeledConfigurationSet.fold foreach_conf confs x
    | (None, label) ->
      let foreach_state q x =
        fold_configurations_for_binding func (Some q, label) t x
      in
      fold_states foreach_state t x

  let iter_configurations_for_binding f ty t =
    fold_configurations_for_binding (fun c q () -> f c q) ty t ()

  let fold_configurations_for_epsilon_state func q a x =
    let table = Hashtbl.create 8 in
    let rec fold_state q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        let fold_conf (conf, _) x =
          match conf with
          | Configuration.Var q' ->
            let x = func conf x in
            fold_state q' x
          | _ -> func conf x
        in
        LabeledConfigurationSet.fold (fold_conf) (configurations_for_state q a) x
    in
    fold_state q x

  let iter_configurations_for_epsilon_state f q a =
    fold_configurations_for_epsilon_state (fun c () -> f c) q a ()

  let list_map_opt f l =
    let for_each_element e = function
      | Some acc ->
        begin
          match f e with
          | Some e -> Some (e::acc)
          | None -> None
        end
      | None -> None
    in
    List.fold_right for_each_element l (Some [])

  let rec list_map2_opt f l1 l2 =
    match l1, l2 with
    | [], [] -> Some []
    | e1::l1, e2::l2 ->
      begin
        match list_map2_opt f l1 l2 with
        | Some l ->
          begin
            match f e1 e2 with
            | Some e -> Some (e::l)
            | None -> None
          end
        | None -> None
      end
    | _, _ -> None

  let rec type_term_in (q : State.t) term t =
    (* let module Term = Term.Make (Sym) in *)
    (* Format.printf "term %t" (Term.print term); *)

    let visited = Hashtbl.create 8 in (* to avoid epsilon loops *)
    let rec ignore_epsilon q (Term.Term (f, l)) =
      match Hashtbl.find_opt visited q with
      | Some () -> None
      | None ->
        let rec type_subterm conf (Term.Term (f, l)) =
          match conf with
          | Configuration.Cons (f', l') when Sym.compare f' f = 0 ->
            begin
              match list_map2_opt type_subterm l' l with
              | Some l -> Some (BoundTerm.Term (f, l), (None, None))
              | None -> None
            end
          | Configuration.Var q' ->
            type_term_in q' (Term.Term (f, l)) t
          | _ -> None
        in
        let fold_cons (conf, label) = function
          | Some typed_term -> Some typed_term
          | None ->
            begin
              match conf with
              | Configuration.Cons (f', l') when Sym.compare f' f = 0 ->
                begin
                  match list_map2_opt type_subterm l' l with
                  | Some l -> Some (BoundTerm.Term (f, l), (Some q, Some label))
                  | None -> None
                end
              | _ -> None
            end
        in
        let fold_epsilon (conf, label) = function
          | Some typed_term -> Some typed_term
          | None ->
            begin
              match conf with
              | Configuration.Var q' ->
                begin
                  match ignore_epsilon q' (Term.Term (f, l)) with
                  | Some typed_term -> Some (BoundTerm.Cast typed_term, (Some q, Some label))
                  | None -> None
                end
              | _ -> None
            end
        in
        Hashtbl.add visited q ();
        let confs = configurations_for_state q t in
        begin
          match LabeledConfigurationSet.fold fold_cons confs None with
          | Some typed_term -> Some typed_term
          | None -> LabeledConfigurationSet.fold fold_epsilon confs None
        end
    in
    ignore_epsilon q term

  let rec recognizes_in q term t =
    let visited = Hashtbl.create 8 in (* to avoid epsilon loops *)
    let rec ignore_epsilon q (Term.Term (f, l)) =
      match Hashtbl.find_opt visited q with
      | Some () -> false
      | None ->
        let rec fold_subconf conf (Term.Term (f, l)) = function
          | false -> false
          | true ->
            begin
              match conf with
              | Configuration.Var q' -> recognizes_in q' (Term.Term (f, l)) t
              | Configuration.Cons (f', l') when Sym.compare f' f = 0 ->
                List.fold_right2 (fold_subconf) l' l true
              | _ -> false
            end
        in
        let fold_conf (conf, _) = function
          | true -> true
          | false ->
            begin
              match conf with
              | Configuration.Var q' -> ignore_epsilon q' (Term.Term (f, l))
              | Configuration.Cons (f', l') when Sym.compare f' f = 0 ->
                List.fold_right2 (fold_subconf) l' l true
              | _ -> false
            end
        in
        Hashtbl.add visited q ();
        let confs = configurations_for_state q t in
        LabeledConfigurationSet.fold (fold_conf) confs false
    in
    ignore_epsilon q term

  let recognizes_state_in q target t =
    let visited = Hashtbl.create 8 in (* to avoid epsilon loops *)
    let rec ignore_epsilon q =
      if State.equal q target then true else
        match Hashtbl.find_opt visited q with
        | Some () -> false
        | None ->
          Hashtbl.add visited q ();
          let fold_conf (conf, _) = function
            | true -> true
            | false ->
              begin
                match conf with
                | Configuration.Var q' -> ignore_epsilon q'
                | _ -> false
              end
          in
          let confs = configurations_for_state q t in
          LabeledConfigurationSet.fold (fold_conf) confs false
    in
    ignore_epsilon q

  let type_term term t =
    let fold_state q = function
      | Some typed_term -> Some typed_term
      | None -> type_term_in q term t
    in
    StateSet.fold fold_state (final_states t) None

  let recognizes term t =
    StateSet.exists (function q -> recognizes_in q term t) (final_states t)

  let label f default _ = (* FIXME why is the automaton not used? *)
    let table = Hashtbl.create 8 in
    let rec label q : 'a =
      match Hashtbl.find_opt table q with
      | Some (Some v) -> v (* label is already computed *)
      | Some (None) -> default q (* label is being computed (cycle) *)
      | None -> (* label is not computed *)
        Hashtbl.add table q None;
        let v = f label q in
        Hashtbl.add table q (Some v);
        v
    in label

  type normalizer = Sym.t -> State.t list -> LabeledState.t

  (** Return [a] and a state+label in [a] that recognises [conf] normalised. *)
  let rec normalize_to_state ?hook (create_state : normalizer) aref (conf : Configuration.t) : BoundConfiguration.t =
    let id = ref 0 in
    let next_var typ =
      let x = Var.of_int !id in
      id := !id + 1;
      BoundConfiguration.Var x, typ
    in
    let normalize = function
      | Configuration.Cons (f, l) ->
        let subs = (List.map (normalize_to_state ?hook create_state aref) l) in
        let typof = function
          | _, (Some q, _) -> q
          | _ -> failwith "normalization failed."
        in
        let sub_types = List.map typof subs in
        let conf = Configuration.Cons (f, List.map Configuration.of_var sub_types) in
        let states = states_for_configuration conf !aref in
        if LabeledStateSet.is_empty states then
          let (q, label) = create_state f sub_types in
          aref := add_transition ?hook conf label q !aref;
          BoundConfiguration.Cons (f, subs), (Some q, Some label)
        else
          let (q, l) = LabeledStateSet.choose states in
          BoundConfiguration.Cons (f, subs), (Some q, Some l)
      | Configuration.Var q -> next_var (Some q, None)
    in
    normalize conf

  and normalized_configuration ?hook create_state conf a =
    match conf with
    | Configuration.Cons (f, l) ->
      let aut = ref a in
      (BoundConfiguration.Cons (f, (List.map (normalize_to_state ?hook create_state aut) l)), (None, None)), !aut
    | Configuration.Var q -> (BoundConfiguration.Var (Var.of_int 0), (Some q, None)), a

  and add_normalized_transition ?hook normalizer conf label q a =
    let conf, a = normalized_configuration ?hook normalizer conf a in
    add_transition ?hook (untyped_configuration conf) label q a

  let add_normalized_transitions ?hook normalizer l a =
    List.fold_left (fun a' (conf, label, q) -> add_normalized_transition ?hook normalizer conf label q a') a l

  let add_configurations_to ?normalizer ?hook lbl_confs q a =
    let add = match normalizer with
      | Some normalizer -> add_normalized_transition normalizer ?hook
      | None -> add_transition ?hook
    in
    List.fold_left (fun a' (conf, label) -> add conf label q a') a lbl_confs

  let add_configuration norm ?hook (conf : Configuration.t) a : BoundConfiguration.t * t =
    let aut = ref a in
    let q = normalize_to_state ?hook norm aut conf in
    (q, !aut)

  let add norm ?hook conf a =
    let conf, a = add_configuration norm ?hook conf a in
    match conf with
    | _, (Some q, _) -> (conf, add_final_state q a)
    | _, (None, _) -> failwith "normalization failed."

  let map ?filter f_label f_state a =
    let map_label = Hashtbl.create 8 in (* 8: arbitrary size *)
    let map_state = Hashtbl.create 8 in (* 8: arbitrary size *)
    let f_label = find_or_create f_label map_label in
    let f_state = find_or_create f_state map_state in
    let rec f_conf = function
      | Configuration.Cons (f, l) -> Configuration.Cons (f, (List.map (f_conf) l))
      | Configuration.Var q -> Configuration.Var (f_state q)
    in
    let add conf label q b =
      let conf = f_conf conf in
      let label = f_label label in
      let q = f_state q in
      let accept = match filter with
        | Some f -> f conf label q b
        | None -> true
      in
      if accept then
        add_transition conf label q b
      else
        b
    in
    let aut = fold_transitions add a (clear a) in
    let add_final q b =
      add_final_state (f_state q) b
    in
    StateSet.fold add_final (final_states a) aut

  let filter p t =
    let add conf label q aut =
      if p conf label q then
        add_transition_unchecked conf label q aut
      else
        aut
    in
    let aut = fold_transitions add t (clear t) in
    let add_final q aut =
      add_final_state q aut
    in
    StateSet.fold add_final (final_states t) aut

  let sub_automaton states t =
    let visited = Hashtbl.create 8 in
    let rec visit_state q u =
      match Hashtbl.find_opt visited q with
      | Some () -> u
      | None ->
        Hashtbl.add visited q ();
        let confs = configurations_for_state q t in
        let add_conf (conf, label) u =
          let u = add_transition conf label q u in
          visit_conf conf u
        in
        LabeledConfigurationSet.fold add_conf confs u
    and visit_conf conf u =
      match conf with
      | Configuration.Cons (_, l) ->
        List.fold_right visit_conf l u
      | Configuration.Var q ->
        visit_state q u
    in
    StateSet.fold visit_state states (set_final_states states (clear t))

  let merge a b =
    let b = fold_transitions (
        fun conf label q b ->
          add_transition conf label q b
      ) a b
    in
    add_final_states (final_states a) b

    let inter ?hook data_product a b =
      (*		let map = Hashtbl.create 8 in (* 8: arbitrary size *)*)
      (*		let state_product a b = find_or_create (function (a, b) -> State.product a b) map (a, b) in*)
      let product qa qa_confs qb qb_confs aut =
        match State.product qa qb with
        | Some q ->
          let labeled_conf_product (ca, la) (cb, lb) aut =
            match (Configuration.product ca cb), (Label.product la lb) with
            | Some conf, Some label -> add_transition conf label q aut
            | None, Some label ->
              begin
                match ca, cb with
                | Configuration.Var qa', _ ->
                  begin
                    match State.product qa' qb with
                    | Some q' -> add_transition (Configuration.Var q') label q aut
                    | None -> aut
                  end
                | _, Configuration.Var qb' ->
                  begin
                    match State.product qa qb' with
                    | Some q' -> add_transition (Configuration.Var q') label q aut
                    | None -> aut
                  end
                | _, _ -> aut
              end
            | _, None -> aut
          in
          print_endline "begin confs";
          (*print_endline (State.print qa Format.str_formatter; Format.flush_str_formatter ());
            print_endline (State.print qb Format.str_formatter; Format.flush_str_formatter ());*)
          print_endline (string_of_int (LabeledConfigurationSet.fold (fun _ s -> s+1) qa_confs 0));
            print_endline (string_of_int (LabeledConfigurationSet.fold (fun _ s -> s+1) qb_confs 0));
          print_endline "end confs";
          let aut = LabeledConfigurationSet.fold2 (labeled_conf_product) (qa_confs) (qb_confs) aut in
          begin
            match hook with
            | Some h -> h aut q
            | None -> ()
          end;
          aut
        | None -> aut
      in
      let add_final qa qb aut =
        match State.product qa qb with
        | Some q -> add_final_state q aut
        | None -> aut
      in

      print_endline "aut begin";
      let aut = StateMap.fold2 product (configurations_for_states a) (configurations_for_states b) (create (data_product (data a) (data b))) in
      print_endline "aut done";
      let a = StateSet.fold2 add_final (final_states a) (final_states b) aut in
      print_endline "final done";
      a

  let reachable_states ?(epsilon=true) a =
    let visited = Hashtbl.create 8 in
    let reachable set c = StateSet.mem c set in
    let rec reach_conf conf set =
      reach_conf_states conf (states_for_configuration conf a) set
    and reach_conf_states conf lbl_states set =
      let fold (q, _) set =
        match Hashtbl.find_opt visited q with
        | Some () -> set
        | None ->
          Hashtbl.add visited q ();
          ConfigurationSet.fold (reach_conf) (state_parents q a) (StateSet.add q set)
      in
      if (epsilon || Configuration.is_cons conf) && (Configuration.for_all (reachable set) conf) then
        LabeledStateSet.fold (fold) lbl_states set
      else set
    in
    ConfigurationMap.fold (reach_conf_states) ((states_for_configurations a)) (StateSet.empty)

  let reduce ?(epsilon=true) ?(from_finals=true) t =
    let reachable_states = reachable_states ~epsilon t in
    let is_reachable_state q = StateSet.mem q reachable_states in
    let is_reachable_conf = Configuration.for_all is_reachable_state in
    let for_each_transition conf label q rt =
      if is_reachable_state q && is_reachable_conf conf then
        add_transition conf label q rt
      else rt
    in
    let rt = fold_transitions for_each_transition t (clear t) in
    let for_each_final_state q rt =
      if is_reachable_state q then
        add_final_state q rt
      else rt
    in
    if from_finals then
      StateSet.fold for_each_final_state (final_states t) rt
    else
      fold_states for_each_final_state t rt
  (* let reachable_set = reachable_states ~epsilon a in
     let is_reachable_state q = StateSet.mem q reachable_set in
     let is_reachable_conf c = Configuration.for_all (is_reachable_state) c in
     let visited = Hashtbl.create 8 in

     (* Build the automaton removing non-reachable states/confs. *)
     let rec build_conf aut conf =
     match conf with (* Assuming conf is reachable. *)
     | Configuration.Cons (f, l) ->
      List.fold_left (build_conf) aut l
     | Configuration.Var q ->
      build_state q aut
     and build_state q aut =
     match Hashtbl.find_opt visited q with
     | Some () -> aut
     | None ->
      Hashtbl.add visited q ();
      if is_reachable_state q then
        let add_and_build (conf, label) aut =
          if is_reachable_conf conf then
            build_conf (add_transition conf label q aut) conf
          else aut
        in
        LabeledConfigurationSet.fold (add_and_build) (configurations_for_state q a) aut
      else aut
     in

     (* First we build the reduced automaton from the roots. *)
     let aut = StateSet.fold (build_state) (a.roots) (empty) in
     (* Then we add the final states. *)
     let add_final q aut = if is_reachable_state q then add_final_state q aut else aut in
     StateSet.fold (add_final) (a.roots) aut *)

  (* let all label q alphabet =
     let add_cons t f =
      let l = List.init (Sym.arity f) (function _ -> Configuration.Var q) in
      add_transition (Configuration.Cons (f, l)) label q t
     in
     List.fold_left add_cons (add_final_state q empty) alphabet *)

  let alphabet t =
    let rec fold_conf conf alphabet =
      match conf with
      | Configuration.Cons (f, l) ->
        List.fold_right fold_conf l (SymSet.add f alphabet)
      | Configuration.Var _ -> alphabet
    in
    let fold_transition conf _ _ alphabet =
      fold_conf conf alphabet
    in
    fold_transitions fold_transition t SymSet.empty

  let complete ?(with_states=StateSet.empty) get_state abc t =
    let states = StateSet.union with_states (states t) in
    let for_each_symbol t f =
      let for_each_word word t =
        let l = List.map (function q -> Configuration.Var q) word in
        let conf = Configuration.Cons (f, l) in
        if LabeledStateSet.is_empty (states_for_configuration conf t) then
          let r, label = get_state conf in
          add_transition conf label r t
        else t
      in
      StateSet.fold_words (Sym.arity f) for_each_word states t
    in
    List.fold_left for_each_symbol t abc

  let complement cdt =
    let states = states cdt in
    let new_final_states = StateSet.diff states (final_states cdt) in
    set_final_states new_final_states cdt

  let unepsilon _ =
    failwith "TODO: unepsilon: Not implemented yet."

  let determinise ?init_classes map_class t =
    let module DetState = struct
      include StateSet

      let print t fmt =
        Format.fprintf fmt "{%t}" (StateSet.print State.print "," t)

      let product a b =
        let c = product State.product a b in
        if is_empty c then
          None
        else
          Some c
    end in
    let module DetConfiguration = Pattern.Make (Sym) (DetState) in
    let module DetTransition = struct
      type t = DetConfiguration.t * Label.t * DetState.t

      let compare (a, la, qa) (b, lb, qb) =
        let c = DetState.compare qa qb in
        if c = 0 then
          let c = Label.compare la lb in
          if c = 0 then DetConfiguration.compare a b
          else c
        else c

      (* let print (conf, _, q) fmt =
         Format.fprintf fmt "%t -> %t" (DetConfiguration.print conf) (DetState.print q) *)
    end in
    let module DetTransitionSet = Set.Make (DetTransition) in
    let module DetStateSet = Set.Make (DetState) in
    let table = Hashtbl.create 8 in
    let classes_of classes q =
      DetStateSet.filter (DetState.mem q) classes
    in
    let add_state q labeled_det_conf =
      let klass = match Hashtbl.find_opt table labeled_det_conf with
        | Some klass ->
          DetState.add q klass
        | None ->
          DetState.singleton q
      in
      Hashtbl.replace table labeled_det_conf klass
    in
    (* TODO optimize the collect function, by not folding ALL transitions,
       but only the transitions containing at least one state in a klass that has just been created.
       If it does not, we already have visited this det-transitions. *)
    let rec collect classes det_transitions =
      fold_transitions (
        fun conf label q () ->
          match conf with
          | Configuration.Cons (f, l) ->
            let possibles_det_l = List.map (classes_of classes) (List.map Configuration.normalized l) in
            DetStateSet.fold_inline_combinations (
              fun det_l () ->
                let labeled_det_conf = (DetConfiguration.Cons (f, List.map DetConfiguration.of_var det_l), label) in
                add_state q labeled_det_conf
            ) possibles_det_l ()
          | Configuration.Var _ ->
            raise (Invalid_argument "Input is not a NFTA.")
      ) t ();
      let new_det_transitions, new_classes = Hashtbl.fold (
          fun (det_conf, label) klass (det_transitions, classes) ->
            let new_det_transitions = DetTransitionSet.add (det_conf, label, klass) det_transitions in
            let new_classes = DetStateSet.add klass classes in
            new_det_transitions, new_classes
        ) table (det_transitions, classes)
      in
      if DetTransitionSet.cardinal new_det_transitions = DetTransitionSet.cardinal det_transitions then
        new_det_transitions, classes
      else
        begin
          Hashtbl.clear table;
          collect new_classes new_det_transitions
        end
    in
    let is_empty q =
      LabeledConfigurationSet.is_empty (configurations_for_state q t)
    in
    let init_classes = match init_classes with
      | Some classes -> StateSet.fold (fun q det_states -> DetStateSet.add (DetState.singleton q) det_states) classes DetStateSet.empty
      (* We put the empty states in their own classes. *)
      | None -> StateSet.fold (fun q det_states -> DetStateSet.add (DetState.singleton q) det_states) (StateSet.filter is_empty (states t)) DetStateSet.empty
    in
    let det_transitions, classes = collect init_classes DetTransitionSet.empty in
    (* mapping time *)
    let map_table = Hashtbl.create (DetStateSet.cardinal classes) in
    let mapped_class k =
      match Hashtbl.find_opt map_table k with
      | Some q -> q
      | None ->
        let q = map_class k in
        Hashtbl.replace map_table k q;
        q
    in
    (* Format.printf "det transitions:\n%t@." (DetTransitionSet.print DetTransition.print "\n" det_transitions); *)
    DetTransitionSet.fold (
      fun (det_conf, label, klass) u ->
        match det_conf with
        | DetConfiguration.Cons (f, det_l) ->
          let l = List.map mapped_class (List.map DetConfiguration.normalized det_l) in
          let conf = Configuration.Cons (f, List.map Configuration.of_var l) in
          let q = mapped_class klass in
          let a = add_transition conf label q u in
          if DetState.for_all (is_final t) klass then
            add_final_state q a
          else
            a
        | DetConfiguration.Var _ ->
          failwith "deteminised automaton is not a NFTA. This is a bug."
    ) det_transitions (clear t)

  (* Determinise typed states automaton.
     States with different types will not be placed in the same equivalence class. *)
  let determinise_typed (type ty) ?init_classes (type_mod : (module TYPE with type t = ty)) (type_of : State.t -> ty) map_class t =
    let module Type : TYPE with type t = ty = (val type_mod) in
    let module DetState = struct
      type t = StateSet.t * Type.t

      let compare (sa, ta) (sb, tb) =
        let c = Type.compare ta tb in
        if c = 0 then StateSet.compare sa sb else c

      let equal (sa, ta) (sb, tb) =
        Type.equal ta tb && StateSet.equal sa sb

      let print (states, ty) fmt =
        Format.fprintf fmt "{%t}:%t" (StateSet.print State.print "," states) (Type.print ty)

      let product (sa, ta) (sb, tb) =
        match Type.product ta tb with
        | Some ty ->
          let states = StateSet.product State.product sa sb in
          if StateSet.is_empty states then
            None
          else
            Some (states, ty)
        | None -> None

      let hash = Hashtbl.hash

      let matches q (states, ty) =
        Type.equal (type_of q) ty && StateSet.mem q states

      let add q (states, ty) =
        StateSet.add q states, ty

      let singleton q =
        StateSet.singleton q, type_of q
    end in
    let module DetConfiguration = Pattern.Make (Sym) (DetState) in
    let module DetTransition = struct
      type t = DetConfiguration.t * Label.t * DetState.t

      let compare (a, la, qa) (b, lb, qb) =
        let c = DetState.compare qa qb in
        if c = 0 then
          let c = Label.compare la lb in
          if c = 0 then DetConfiguration.compare a b
          else c
        else c

      (* let print (conf, _, q) fmt =
         Format.fprintf fmt "%t -> %t" (DetConfiguration.print conf) (DetState.print q) *)
    end in
    let module DetTransitionSet = Set.Make (DetTransition) in
    let module DetStateSet = Set.Make (DetState) in
    let table = Hashtbl.create 8 in
    let classes_of classes q =
      DetStateSet.filter (DetState.matches q) classes
    in
    let add_state q labeled_det_conf =
      let ty = type_of q in
      let klass = match Hashtbl.find_opt table (labeled_det_conf, ty) with
        | Some klass ->
          DetState.add q klass
        | None ->
          DetState.singleton q
      in
      Hashtbl.replace table (labeled_det_conf, ty) klass
    in
    (* TODO optimize the collect function, by not folding ALL transitions,
       but only the transitions containing at least one state in a klass that has just been created.
       If it does not, we already have visited this det-transitions. *)
    let rec collect classes det_transitions =
      fold_transitions (
        fun conf label q () ->
          match conf with
          | Configuration.Cons (f, l) ->
            let possibles_det_l = List.map (classes_of classes) (List.map Configuration.normalized l) in
            DetStateSet.fold_inline_combinations (
              fun det_l () ->
                let labeled_det_conf = (DetConfiguration.Cons (f, List.map DetConfiguration.of_var det_l), label) in
                add_state q labeled_det_conf
            ) possibles_det_l ()
          | Configuration.Var _ ->
            raise (Invalid_argument "Input is not a NFTA.")
      ) t ();
      let new_det_transitions, new_classes = Hashtbl.fold (
          fun ((det_conf, label), _) klass (det_transitions, classes) -> (* TODO *)
            let new_det_transitions = DetTransitionSet.add (det_conf, label, klass) det_transitions in
            let new_classes = DetStateSet.add klass classes in
            new_det_transitions, new_classes
        ) table (det_transitions, classes)
      in
      if DetTransitionSet.cardinal new_det_transitions = DetTransitionSet.cardinal det_transitions then
        new_det_transitions, classes
      else
        begin
          Hashtbl.clear table;
          collect new_classes new_det_transitions
        end
    in
    let is_empty q =
      LabeledConfigurationSet.is_empty (configurations_for_state q t)
    in
    let init_classes = match init_classes with
      | Some classes -> StateSet.fold (fun q det_states -> DetStateSet.add (DetState.singleton q) det_states) classes DetStateSet.empty
      (* We put the empty states in their own classes. *)
      | None -> StateSet.fold (fun q det_states -> DetStateSet.add (DetState.singleton q) det_states) (StateSet.filter is_empty (states t)) DetStateSet.empty
    in
    let det_transitions, classes = collect init_classes DetTransitionSet.empty in
    (* mapping time *)
    let map_table = Hashtbl.create (DetStateSet.cardinal classes) in
    let mapped_class k =
      match Hashtbl.find_opt map_table k with
      | Some q -> q
      | None ->
        let states, ty = k in
        let q = map_class states ty in
        Hashtbl.replace map_table k q;
        q
    in
    (* Format.printf "det transitions:\n%t@." (DetTransitionSet.print DetTransition.print "\n" det_transitions); *)
    DetTransitionSet.fold (
      fun (det_conf, label, klass) u ->
        match det_conf with
        | DetConfiguration.Cons (f, det_l) ->
          let l = List.map mapped_class (List.map DetConfiguration.normalized det_l) in
          let conf = Configuration.Cons (f, List.map Configuration.of_var l) in
          let q = mapped_class klass in
          add_transition conf label q u
        | DetConfiguration.Var _ ->
          failwith "deteminised automaton is not a NFTA. This is a bug."
    ) det_transitions (clear t)

  module StateUnionFind = UnionFind.Make (State) (StateSet)

  exception Found_equiv of State.t * State.t

  let find_equiv_opt filter t =
    (* let open Log in *)
    (* checks if [q'] is semi-equiv to [q]. *)
    let semi_equiv q q' =
      (* This function is used to map a set of states so that [q'] is mapped to [q]. *)
      let reduced labeled_states =
        LabeledStateSet.map (
          function (q'', label) ->
            let q'' = if State.equal q'' q' then q else q'' in
            q'', label
        ) labeled_states
      in
      let expected_states = Hashtbl.create 8 in
      (* All the configurations in which q appears. *)
      let q_confs = state_parents q t in
      (* Now we compute all the configurations in which q' should appear. *)
      let q'_confs = ConfigurationSet.map (
          function
          | Configuration.Cons (f, l) ->
            let l' = List.map (
                function
                | Configuration.Var sub_q when State.equal q sub_q -> Configuration.Var q'
                | Configuration.Var sub_q -> Configuration.Var sub_q
                | _ -> raise (Invalid_argument "automaton must be normalized")
              ) l
            in
            let conf' = Configuration.Cons (f, l') in
            (* [states] contains all the states in which this configuration should appear. *)
            let states = states_for_configuration (Configuration.Cons (f, l)) t in
            Hashtbl.add expected_states conf' (reduced states);
            conf'
          | _ -> raise (Invalid_argument "automaton must be normalized")
        ) q_confs
      in
      (* Check that those configurations indeed are in the automaton... *)
      ConfigurationSet.equal q'_confs (state_parents q' t) &&
      (* ...and that. *)
      ConfigurationSet.for_all (
        function conf' ->
          let states' = states_for_configuration conf' t in
          LabeledStateSet.equal (reduced states') (Hashtbl.find expected_states conf')
      ) q'_confs
    in
    try
      fold_states (
        fun q () ->
          fold_states (
            fun q' () ->
              if not (State.equal q q') && (filter q q') then
                begin
                  (* debug "min testing %t %t@." (State.print q) (State.print q'); *)
                  if semi_equiv q q' && semi_equiv q' q then
                    begin
                      (* debug "eq@."; *)
                      raise (Found_equiv (q, q'))
                    end
                end
          ) t ()
      ) t ();
      None
    with
    | Found_equiv (q, q') -> Some (q, q')

  (* Minimalise the automaton. *)
  let rec minimalise ?(filter=fun _ _ -> true) t =
    begin match find_equiv_opt filter t with
      | Some (q, q') ->
        let map_label l = l in
        let map_state q'' = if State.equal q'' q' then q else q'' in
        let t = map map_label map_state t in
        minimalise ~filter t
      | None ->
        t
    end

  let prune_useless (x:t)
    : t =
    print_endline "min-red sub";
    let x = reduce x in
    print_endline "prune final";
    let fs = final_states x in
    let x = sub_automaton fs x in
      print_endline "prune done";
    (*minimalise*) x

  (*let top_down_inter
      (x:t)
      (y:t)
    : t =
    let visited = Hashtbl.create 8 in
    let rec visit_state qx qy u =
      let q = State.product q1 q2 in
      match Hashtbl.find_opt visited q with
      | Some () -> u
      | None ->
        let confsx = configurations_for_state q1 x in
        let confsy = configurations_for_state q1 y in
        labeled_conf_product confsx confsy u
    and labeled_conf_product (ca, la) (cb, lb) aut =
      match (Configuration.product ca cb), (Label.product la lb) with
      | Some conf, Some label -> add_transition conf label q aut
          | None, Some label ->
            begin
              match ca, cb with
              | Configuration.Var qa', _ ->
                begin
                  match State.product qa' qb with
                  | Some q' -> add_transition (Configuration.Var q') label q aut
                  | None -> aut
                end
              | _, Configuration.Var qb' ->
                begin
                  match State.product qa qb' with
                  | Some q' -> add_transition (Configuration.Var q') label q aut
                  | None -> aut
                end
              | _, _ -> aut
            end
          | _, None -> aut
        in


  let visited = Hashtbl.create 8 in
  let rec visit_state q u =
    match Hashtbl.find_opt visited q with
    | Some () -> u
    | None ->
      Hashtbl.add visited q ();
      let confs = configurations_for_state q t in
      let add_conf (conf, label) u =
        let u = add_transition conf label q u in
        visit_conf conf u
      in
      LabeledConfigurationSet.fold add_conf confs u
  and visit_conf conf u =
    match conf with
    | Configuration.Cons (_, l) ->
      List.fold_right visit_conf l u
    | Configuration.Var q ->
      visit_state q u
  in
  StateSet.fold visit_state states (set_final_states states (clear t))
    let fx = final_states x in
    let fy = final_states y in
    failwith "ah"*)

  type renaming = State.t StateMap.t

  exception Found of renaming

  let rec state_renaming ?(knowledge=StateMap.empty) a b qa qb =
    match StateMap.find_opt qb knowledge with
    | Some q when State.equal qa q -> Some knowledge
    | Some _ -> None
    | None ->
      begin
        (* NOTE idea: Use MurmurHash to hash the structure of each state. *)
        let match_confs (qa_conf, qa_label) (qb_conf, qb_label) knowledge =
          if Label.equal qa_label qb_label then
            match qa_conf, qb_conf with
            | Configuration.Cons (fa, la), Configuration.Cons (fb, lb) when Sym.equal fa fb ->
              begin
                try
                  let knowledge = List.fold_right2 (
                      fun qa' qb' knowledge ->
                        match state_renaming ~knowledge a b qa' qb' with
                        | Some knowledge -> knowledge
                        | None -> raise Not_found
                    ) (List.map Configuration.normalized la) (List.map Configuration.normalized lb) knowledge
                  in
                  Some knowledge
                with
                | Not_found -> None
              end
            | Configuration.Var qa', Configuration.Var qb' ->
              state_renaming ~knowledge a b qa' qb'
            | _ -> None
          else
            None
        in
        try
          let qa_confs = configurations_for_state qa a in
          let qb_confs = configurations_for_state qb b in
          if LabeledConfigurationSet.cardinal qa_confs = LabeledConfigurationSet.cardinal qb_confs then
            try
              let rec find_renaming qa_confs qb_confs knowledge =
                if LabeledConfigurationSet.is_empty qa_confs then
                  raise (Found knowledge)
                else
                  begin
                    let qa_conf = LabeledConfigurationSet.choose qa_confs in
                    LabeledConfigurationSet.iter (
                      function qb_conf ->
                      match match_confs qa_conf qb_conf knowledge with
                      | Some knowledge ->
                        begin
                          let qa_confs = LabeledConfigurationSet.remove qa_conf qa_confs in
                          let qb_confs = LabeledConfigurationSet.remove qb_conf qb_confs in
                          try find_renaming qa_confs qb_confs knowledge with
                          | Not_found -> ()
                        end
                      | None -> ()
                    ) qb_confs;
                    raise Not_found
                  end
              in
              find_renaming qa_confs qb_confs (StateMap.add qb qa knowledge);
              None
            with
            | Found knowledge -> Some knowledge
          else
            raise Not_found
        with
        | Not_found -> None
      end

  let of_term norm t data =
    let (_, a) = add norm (Configuration.of_term t) (create data) in
    a

  let of_terms norm l data =
    let add_term a term =
      let (_, a) = add norm (Configuration.of_term term) a in
      a
    in
    List.fold_left (add_term) (create data) l

  let compare a b =
    let c = StateSet.compare (final_states a) (final_states b) in
    if c = 0 then StateMap.compare (LabeledConfigurationSet.compare) (configurations_for_states a) (configurations_for_states b) else c

  let print t out =
    let print_state_confs q confs =
      let print_conf conf =
        Format.fprintf out "%t -> %t\n" (LabeledConfiguration.print conf) (State.print q)
      in
      LabeledConfigurationSet.iter (print_conf) confs
    and print_state q =
      Format.fprintf out "%t " (State.print q)
    in
    StateMap.iter print_state_confs (configurations_for_states t);
    Format.fprintf out "final states: ";
    StateSet.iter print_state (final_states t)

  module Patterns (X : Pattern.VARIABLE) = struct
    module Pattern = Pattern.Make (Sym) (X)

    type pattern = Pattern.t

    let rec recognizes_pattern_in q pattern t =
      let visited = Hashtbl.create 8 in (* to avoid epsilon loops *)
      let rec ignore_epsilon q pattern =
        match Hashtbl.find_opt visited q with
        | Some () -> false
        | None ->
          begin
            match pattern with
            | Pattern.Var _ -> true
            | Pattern.Cons (f, l) ->
              let rec fold_subconf conf pattern = function
                | false -> false
                | true ->
                  begin
                    match pattern with
                    | Pattern.Var _ -> true
                    | Pattern.Cons (f, l) ->
                      begin
                        match conf with
                        | Configuration.Var q' -> recognizes_pattern_in q' pattern t
                        | Configuration.Cons (f', l') when Sym.compare f' f = 0 ->
                          List.fold_right2 (fold_subconf) l' l true
                        | _ -> false
                      end
                  end
              in
              let fold_conf (conf, _) = function
                | true -> true
                | false ->
                  begin
                    match conf with
                    | Configuration.Var q' -> ignore_epsilon q' pattern
                    | Configuration.Cons (f', l') when Sym.compare f' f = 0 ->
                      List.fold_right2 (fold_subconf) l' l true
                    | _ -> false
                  end
              in
              Hashtbl.add visited q ();
              let confs = configurations_for_state q t in
              LabeledConfigurationSet.fold (fold_conf) confs false
          end
      in
      ignore_epsilon q pattern

    let recognizes_pattern pattern t =
      StateSet.exists (function q -> recognizes_pattern_in q pattern t) (final_states t)

    let rec configuration_of_pattern state = function
      | Pattern.Cons (f, l) -> Configuration.Cons (f, List.map (configuration_of_pattern state) l)
      | Pattern.Var x -> Configuration.Var (state x)
  end

  module StateTable = HashTable.Make (State)

  type dynamic_filter =
    | NoFilter
    | Filter of (State.t -> Label.t -> (bool * dynamic_filter))

  let fold_type_inhabitants ?(epsilon_f=None) ?(filter=NoFilter) g typ t x =
    let no_path_table = Hashtbl.create 8 in
    let rec fold filter g visited typ x =
      let call_filter q label = match filter with
        | Filter f -> f q label
        | NoFilter -> true, NoFilter
      in
      match Hashtbl.find_opt no_path_table typ with
      | Some () -> x
      | None ->
        begin
          let path_found = ref false in
          let path_skipped = ref false in
          let g t x =
            path_found := true;
            g t x
          in
          let epsilon = match epsilon_f with
            | Some f -> f typ
            | None -> true
          in
          let visit q =
            match StateTable.find_opt q visited with
            | Some () -> visited, false
            | None -> (StateTable.set q () visited), true
          in
          let fold_conf (conf, label) q x =
            let visited, proceed = visit q in
            let accept, new_filter = call_filter q label in
            if proceed && accept then
              begin
                match conf with
                | Configuration.Var _ -> x
                | Configuration.Cons (f, l) ->
                  let rec fold_conf_list g left l x =
                    match l with
                    | [] -> g (BoundTerm.Term (f, List.rev left), (Some q, Some label)) x
                    | sc::l ->
                      let fold_subterm st x =
                        fold_conf_list g (st::left) l x
                      in
                      let rec fold_subconf g subconf x =
                        match subconf with
                        | Configuration.Cons (f', l') ->
                          let rec fold_subconf_list g left' _ x =
                            match l with
                            | [] -> g (BoundTerm.Term (f', List.rev left'), (None, None)) x
                            | sc::l' ->
                              let fold_subsubconf st x =
                                fold_subconf_list g (st::left') l' x
                              in
                              fold_subconf fold_subsubconf sc x
                          in
                          fold_subconf_list g [] l' x
                        | Configuration.Var q' ->
                          fold new_filter g visited (Some q', None) x
                      in
                      fold_subconf fold_subterm sc x
                  in
                  fold_conf_list g [] l x
              end
            else
              begin
                if not proceed then path_skipped := true;
                x
              end
          in
          let fold_epsilon_conf (conf, label) q x =
            let visited, proceed = visit q in
            let accept, new_filter = call_filter q label in
            if proceed && accept then
              begin
                match conf with
                | Configuration.Var q' ->
                  let fold_type_inhabitant term x =
                    g (BoundTerm.Cast term, (Some q, Some label)) x
                  in
                  fold new_filter fold_type_inhabitant visited (Some q', None) x
                | Configuration.Cons _ -> x
              end
            else x
          in
          let x = fold_configurations_for_binding fold_conf typ t x in
          let x = if epsilon && not (!path_found)
            then fold_configurations_for_binding fold_epsilon_conf typ t x
            else x
          in
          if not (!path_found) && not (!path_skipped) then Hashtbl.add no_path_table typ (); (* FIXME TODO NO OVER! WARNING! NOTE! we must take into account the visited table. Maybe there is no path because we rejected some already visited states. *)
          x
        end
    in
    fold filter g (StateTable.create 8) typ x

  (* TODO use fold_type_inhabitants to replace this implementation. *)
  let pick_binding_inhabitant_opt ?(epsilon=true) typ t =
    let rec pick_in visited typ =
      let visit q =
        match StateTable.find_opt q visited with
        | Some () -> visited, false
        | None -> (StateTable.set q () visited), true
      in
      let try_conf (conf, label) q = function
        | Some term -> Some term
        | None ->
          let visited, proceed = visit q in
          if proceed then
            begin
              match conf with
              | Configuration.Var q' when epsilon ->
                begin
                  match pick_in visited (Some q', None) with
                  | Some term -> Some (BoundTerm.Cast term, (Some q, Some label))
                  | None -> None
                end
              | Configuration.Var _ -> None (* not epsilon *)
              | Configuration.Cons (f, l) ->
                begin
                  let rec pick_subterm = function
                    | Configuration.Cons (f', l') ->
                      begin
                        match list_map_opt pick_subterm l' with
                        | Some l' -> Some (BoundTerm.Term (f', l'), (None, None))
                        | None -> None
                      end
                    | Configuration.Var q' ->
                      pick_in visited (Some q', None)
                  in
                  match list_map_opt pick_subterm l with
                  | Some l -> Some (BoundTerm.Term (f, l), (Some q, Some label))
                  | None -> None
                end
            end
          else None
      in
      fold_configurations_for_binding try_conf typ t None
    in
    pick_in (StateTable.create 8) typ

  let instanciate_typed_configuration_opt ?(epsilon=true) conf t =
    let table = Hashtbl.create 8 in
    let rec instanciate conf =
      match conf with
      | BoundConfiguration.Cons (f, l), typ ->
        begin
          match list_map_opt instanciate l with
          | Some l -> Some (BoundTerm.Term (f, l), typ)
          | None -> None
        end
      | BoundConfiguration.Cast conf, typ ->
        begin
          match instanciate conf with
          | Some term -> Some (BoundTerm.Cast term, typ)
          | None -> None
        end
      | BoundConfiguration.Var x, typ ->
        begin
          match Hashtbl.find_opt table x with
          | Some term -> Some term
          | None ->
            begin
              match pick_binding_inhabitant_opt ~epsilon typ t with
              | Some term ->
                Hashtbl.add table x term;
                Some term
              | None -> None
            end
        end
    in
    instanciate conf

  let pick_binding_inhabitant ?(epsilon=true) typ t =
    match pick_binding_inhabitant_opt ~epsilon typ t with
    | Some term -> term
    | None -> raise (Invalid_argument "Automaton.pick_term_in: empty type")

  let pick_term_in_opt ?(epsilon=true) (q: State.t) t =
    pick_binding_inhabitant_opt ~epsilon (Some q, None) t

  let pick_term_in ?(epsilon=true) q t =
    match pick_term_in_opt ~epsilon q t with
    | Some term -> term
    | None -> raise (Invalid_argument "Automaton.pick_term_in: empty state")

  let fold_common_configurations ?(epsilon=true) g states t accu =
    let states = StateSet.elements states in
    let fold_configurations_for_state =
      if epsilon then
        fold_configurations_for_epsilon_state
      else
        fun f q t accu ->
          let confs = configurations_for_state q t in
          LabeledConfigurationSet.fold (
            fun (conf, _) accu ->
              f conf accu
          ) confs accu
    in
    let transpose ll =
      List.transpose (function l -> StateSet.of_list l) ll
    in
    begin match states with
      | [] -> accu
      | q::states ->
        let rec fold_on_symbol f states subs accu =
          begin match states with
            | [] -> g f (transpose subs) accu
            | q::states ->
              fold_configurations_for_state (
                fun conf accu ->
                  match conf with
                  | Configuration.Cons (f', l) when Sym.equal f f' ->
                    let l = List.map Configuration.normalized l in
                    fold_on_symbol f states (l::subs) accu
                  | _ ->
                    accu
              ) q t accu
          end
        in
        fold_configurations_for_state (
          fun conf accu ->
            match conf with
            | Configuration.Cons (f, l) ->
              let l = List.map Configuration.normalized l in
              fold_on_symbol f states [l] accu
            | _ ->
              accu
        ) q t accu
    end

  let iter_common_configurations ?(epsilon=true) g states t =
    fold_common_configurations ~epsilon (fun f l () -> g f l) states t ()

  let pick_term_in_intersection_opt ?(epsilon=true) states t =
    let exception Found of Sym.t Term.term in
    let module StateSetSet = Set.Make (StateSet) in
    let already_found = Hashtbl.create 8 in
    let rec pick visited states =
      (* Format.eprintf "states: %t@." (StateSet.print State.print "," states); *)
      if StateSetSet.mem states visited then
        None
      else
        begin
          match Hashtbl.find_opt already_found states with
          | Some term -> Some term
          | None ->
            begin
              let visited = StateSetSet.add states visited in
              try iter_common_configurations ~epsilon (
                  fun f l ->
                    begin match List.map_opt (pick visited) l with
                      | Some l ->
                        let term = Term.Term (f, l) in
                        Hashtbl.add already_found states term;
                        raise (Found term)
                      | None -> ()
                    end
                ) states t;
                None
              with
              | Found term -> Some term
            end
        end
    in
    pick StateSetSet.empty states

  let pick_term_in_intersection ?(epsilon=true) states t =
    begin match pick_term_in_intersection_opt ~epsilon states t with
      | Some term -> term
      | None -> raise Not_found
    end

  (*let pick_term_opt ?(smallest=false) ?(epsilon=true) t =
    let pick_in q = function
      | Some term ->
        if smallest then
          begin
            match pick_term_in_opt ~epsilon q t with
            | Some other_term ->
              if BoundTerm.size term < BoundTerm.size other_term then
                Some term
              else
                Some other_term
            | None -> Some term
          end
        else
          Some term
      | None -> pick_term_in_opt ~epsilon q t
    in
    StateSet.fold pick_in (final_states t) None*)

  let rec config_to_bt_opt
      (f:State.t -> BoundTerm.t option)
      (c:Configuration.t)
    : BoundTerm.t option =
    begin match c with
      | Var s -> f s
      | Cons(l,cs) ->
        let cs_opt =
          list_map_opt
            (config_to_bt_opt f)
            cs
        in
        begin match cs_opt with
          | None -> None
          | Some bts -> Some (BoundTerm.Term (l,bts),(None,None))
        end
    end


  let reachable_values a =
    let retrieve_computed_value map c = StateMap.find_opt c map in
    let rec find_reachables todos map =
      begin match todos with
        | [] -> map
        | (config,lbl_states)::todos ->
          let bto = config_to_bt_opt (retrieve_computed_value map) config in
          begin match bto with
            | None -> find_reachables todos map
            | Some bt ->
              let (map,new_todos) =
                LabeledStateSet.fold
                  (fun (q,_) (map,new_todos) ->
                     if StateMap.mem q map then
                       (map,new_todos)
                     else
                       let map = StateMap.add q bt map in
                       let new_todos =
                         ConfigurationSet.fold
                           (fun c new_todos ->
                              (c,states_for_configuration c a)::new_todos)
                           (state_parents q a)
                           new_todos
                       in
                       (map,new_todos))
                  lbl_states
                  (map,[])
              in
              find_reachables (todos@new_todos) map
          end
      end
    in
    let initial_todos =
      ConfigurationMap.fold
        (fun c lbl_states acc -> (c,lbl_states)::acc)
        (states_for_configurations a)
        []
    in
    find_reachables initial_todos StateMap.empty

  type 'a picked_in =
    | NoSolution
    | NoSolutionYet
    | Solution of 'a

  let pick_term_in_to_size
      (a:t)
      typ
      (i:int)
      (stable:BoundTerm.t StateTable.t ref)
    : BoundTerm.t picked_in =
    let rec pick_in visited typ i =
      if i = 0 then
        (NoSolutionYet)
      else
        let visit q =
          match StateTable.find_opt q visited with
          | Some () -> visited, false
          | None -> (StateTable.set q () visited), true
        in
        let try_conf (conf, label) q acc =
          begin match acc with
            | Solution term -> (Solution term)
            | NoSolution
            | NoSolutionYet ->
              begin match StateTable.find_opt q !stable with
                | Some s -> Solution s
                | None ->
                  let ans =
                    let visited, proceed = visit q in
                    if proceed then
                      begin
                        match conf with
                        | Configuration.Var q' ->
                          let (soln) = pick_in visited (Some q', None) (i-1) in
                          begin
                            match soln with
                            | Solution term -> (Solution (BoundTerm.Cast term, (Some q, Some label)))
                            | ns -> (ns)
                          end
                        | Configuration.Cons (f, l) ->
                          begin
                            let rec pick_subterm = function
                              | Configuration.Cons (f', l') ->
                                let soln =
                                  List.fold_right
                                    (fun st acc ->
                                       begin match acc with
                                         | NoSolution -> NoSolution
                                         | NoSolutionYet -> NoSolutionYet
                                         | Solution fs ->
                                           begin match pick_subterm st with
                                             | Solution s -> Solution (s::fs)
                                             | NoSolution -> NoSolution
                                             | NoSolutionYet -> NoSolutionYet
                                           end
                                       end)
                                    l'
                                    (Solution [])
                                in
                                begin match soln with
                                  | Solution s -> Solution (BoundTerm.Term (f', s), (None, None))
                                  | NoSolution -> NoSolution
                                  | NoSolutionYet -> NoSolutionYet
                                end
                              | Configuration.Var q' ->
                                pick_in visited (Some q', None) (i-1)
                            in
                            let soln =
                              List.fold_right
                                (fun st acc ->
                                   begin match acc with
                                     | NoSolution -> NoSolution
                                     | NoSolutionYet -> NoSolutionYet
                                     | Solution fs ->
                                       begin match pick_subterm st with
                                         | Solution s -> Solution (s::fs)
                                         | NoSolution -> NoSolution
                                         | NoSolutionYet -> NoSolutionYet
                                       end
                                   end)
                                l
                                (Solution [])
                            in
                            begin match soln with
                              | Solution s -> Solution (BoundTerm.Term (f, s), (None, None))
                              | NoSolution -> acc
                              | NoSolutionYet -> NoSolutionYet
                            end
                          end
                      end
                    else NoSolution
                  in
                  begin match ans with
                    | Solution s -> stable := StateTable.set q s !stable;
                    | _ -> ()
                  end;
                  ans
              end
          end
            in
            fold_configurations_for_binding try_conf typ a NoSolution
    in
    pick_in (StateTable.create 8) typ i

  let pick_term_iterative_deepen t =
    let stable = ref (StateTable.create 8) in
    let rec pick_term_iterative_deepen_num (i:int) =
      let ans =
        StateSet.fold
          (fun s acc ->
             begin match acc with
               | Solution s -> Solution s
               | NoSolution
               | NoSolutionYet ->
                 begin match pick_term_in_to_size t (Some s, None) i stable with
                   | NoSolution -> acc
                   | s -> s
                 end
             end)
          (final_states t)
          NoSolution
      in
      begin match ans with
        | Solution s -> Some s
        | NoSolutionYet -> pick_term_iterative_deepen_num (i+1)
        | NoSolution -> None
      end
    in
    pick_term_iterative_deepen_num 0

  let pick_term_opt ?(smallest=false) ?(epsilon=true) t =
    let _ = smallest in
    let _ = epsilon in
    pick_term_iterative_deepen t

  let pick_term ?(smallest=false) ?(epsilon=true) t =
    let _ = smallest in
    let _ = epsilon in
    begin match pick_term_iterative_deepen t with
      | Some term -> term
      | None -> raise (Invalid_argument "Automaton.pick_term: empty automaton")
    end
    (*match pick_term_opt ~smallest ~epsilon t with
    | Some term -> term
      | None -> raise (Invalid_argument "Automaton.pick_term: empty automaton")*)

  module BoundPatterns (X : Pattern.VARIABLE) = struct
    module BoundPattern = TypedPattern.Make (Sym) (X) (Binding)
    module VarTable = HashTable.Make (X)

    type bound_pattern = BoundPattern.t

    let fold_pattern_instances ?(epsilon_f=None) ?(filter=NoFilter) g (pattern : bound_pattern) t x =
      let compatible_labels a b =
        match a, b with
        | Some a, Some b -> Label.equal a b
        | _, _ -> true
      in
      let rec fold filter g visited (pattern, ptyp) (conf, typ) sigma x =
        let call_filter q label = match filter with
          | Filter f -> f q label
          | NoFilter -> true, NoFilter
        in
        (* if Binding.equal ptyp typ then *)
        begin
          let visit q =
            match StateTable.find_opt q visited with
            | Some () -> visited, false
            | None -> (StateTable.set q () visited), true
          in
          let fold_states g x = match typ with
            | (Some q, _) -> g q x
            | (None, _) -> fold_states g t x
          in
          let epsilon = match epsilon_f with
            | Some f -> f (pattern, ptyp)
            | None -> true
          in
          let label = snd typ in
          let plabel = snd ptyp in
          let target_q = fst ptyp in
          let fold_state q x =
            let visited, proceed = visit q in
            if proceed then
              begin
                match pattern, conf with
                | BoundPattern.Cons (f, l), BoundConfiguration.Var _ ->
                  let confs = configurations_for_state q t in
                  let fold_conf (conf, label') x =
                    let accept, new_filter = call_filter q label' in
                    if accept then
                      match conf with
                      | Configuration.Cons (f', l') when Sym.equal f f'
                                                      && state_typecheck q target_q
                                                      && label_typecheck label' label
                                                      && label_typecheck label' plabel ->
                        let rec fold_list left l l' sigma x =
                          match l, l' with
                          | [], [] ->
                            let term = BoundTerm.Term (f, List.rev left), (Some q, Some label') in
                            g term sigma x
                          | sub_pattern::l, sub_conf::l' ->
                            let fold_sub_instance term sigma x =
                              fold_list (term::left) l l' sigma x
                            in
                            fold new_filter fold_sub_instance (StateTable.create 8) sub_pattern (typed_configuration sub_conf) sigma x
                          | _, _ -> raise (Invalid_argument "malformed term")
                        in
                        fold_list [] l l' sigma x
                      | _ -> x
                    else
                      x (* filtered out *)
                  in
                  let fold_epsilon_conf (conf, label') x =
                    let accept, new_filter = call_filter q label' in
                    if accept then
                      match conf with
                      | Configuration.Var q' ->
                        let fold_instance term sigma x =
                          let term = BoundTerm.Cast term, (Some q, Some label') in
                          g term sigma x
                        in
                        let new_target_q = if state_typecheck q target_q then None else target_q in
                        let new_label = if label_typecheck label' label then None else label in
                        let new_plabel = if label_typecheck label' plabel then None else plabel in
                        fold new_filter fold_instance visited (pattern, (new_target_q, new_plabel)) (BoundConfiguration.Var (Var.of_int 0), (Some q', new_label)) sigma x
                      | _ ->
                        x (* incompatible configuration *)
                    else
                      x (* filtered out *)
                  in
                  let x = LabeledConfigurationSet.fold_random fold_conf confs x in
                  if epsilon then
                    LabeledConfigurationSet.fold fold_epsilon_conf confs x
                  else
                    x
                | BoundPattern.Cast _, _ when not epsilon  ->
                  x (* when not epsilon *)
                | BoundPattern.Cast sub_pattern, BoundConfiguration.Var _ ->
                  let confs = configurations_for_state q t in
                  let fold_conf (conf, label') x =
                    let accept, new_filter = call_filter q label' in
                    if accept then
                      match conf with
                      | Configuration.Var q' when state_typecheck q target_q
                                               && label_typecheck label' label
                                               && label_typecheck label' plabel->
                        let fold_instance term sigma x =
                          let term = BoundTerm.Cast term, (Some q, Some label') in
                          g term sigma x
                        in
                        fold new_filter fold_instance visited sub_pattern (BoundConfiguration.Var (Var.of_int 0), (Some q', None)) sigma x
                      | Configuration.Var q' ->
                        let fold_instance term sigma x =
                          let term = BoundTerm.Cast term, (Some q, Some label') in
                          g term sigma x
                        in
                        let new_target_q = if state_typecheck q target_q then None else target_q in
                        let new_label = if label_typecheck label' label then None else label in
                        let new_plabel = if label_typecheck label' plabel then None else plabel in
                        fold new_filter fold_instance visited (pattern, (new_target_q, new_plabel)) (BoundConfiguration.Var (Var.of_int 0), (Some q', new_label)) sigma x
                      | _ ->
                        x (* incompatible configuration *)
                    else
                      x (* filtered out *)
                  in
                  LabeledConfigurationSet.fold_random fold_conf confs x
                | BoundPattern.Var z, BoundConfiguration.Var z' ->
                  begin
                    if state_typecheck q target_q && compatible_labels label plabel then
                      begin
                        match VarTable.find_opt z sigma with
                        | Some term -> (* TODO check type. [typ] may missmatch the type of [term]. *)
                          g term sigma x
                        | None ->
                          begin
                            let fold_type_inhabitant term x =
                              let sigma = VarTable.set z term sigma in
                              g term sigma x
                            in
                            let epsilon_f = match epsilon_f with
                              | Some f ->  Some (function typ -> f (BoundPattern.Var z, typ))
                              | None -> None
                            in
                            fold_type_inhabitants ~epsilon_f:epsilon_f ~filter fold_type_inhabitant (Some q, plabel) t x
                          end
                      end
                    else
                      begin
                        let confs = configurations_for_state q t in
                        let fold_conf (conf, label') x =
                          let accept, new_filter = call_filter q label' in
                          if accept then
                            match conf with
                            | Configuration.Var q' ->
                              let fold_instance term sigma x =
                                let term = BoundTerm.Cast term, (Some q, Some label') in
                                g term sigma x
                              in
                              let new_target_q = if state_typecheck q target_q then None else target_q in
                              let new_label = if label_typecheck label' label then None else label in
                              let new_plabel = if label_typecheck label' plabel then None else plabel in
                              fold new_filter fold_instance visited (pattern, (new_target_q, new_plabel)) (BoundConfiguration.Var z', (Some q', new_label)) sigma x
                            | _ ->
                              x (* incompatible configuration *)
                          else
                            x (* filtered out *)
                        in
                        LabeledConfigurationSet.fold_random fold_conf confs x
                      end
                  end
                | _, BoundConfiguration.Cast _ ->
                  raise (Invalid_argument "Casts are not allowed in typed configurations.")
                | _, BoundConfiguration.Cons _ ->
                  failwith "fold_pattern_instances: non normalized configurations not handled yet."
              end
            else x (* if the state has been visited already (epsilon-cycle) *)
          in
          fold_states fold_state x
        end
        (* else
           x (* type missmatch *) *)
      in
      fold filter (fun term _ x -> g term x) (StateTable.create 8) pattern (BoundConfiguration.Var (Var.of_int 0), (snd pattern)) (VarTable.create 8) x

    (* let rec fold_pattern_instances ?(epsilon=true) g pattern t x =
       let rec fold g pat sigma x =
        match pat with
        | BoundPattern.Cons (f, l), typ ->
          let rec fold_subpatterns left l sigma x =
            match l with
            | [] -> g (BoundTerm.Term (f, List.rev left), typ) sigma x
            | sp::l ->
              let fold_instance st sigma x =
                fold_subpatterns (st::left) l sigma x
              in
              fold fold_instance sp sigma x
          in
          fold_subpatterns [] l sigma x
        | BoundPattern.Cast pat, typ ->
          let fold_subpattern term sigma x =
            g (BoundTerm.Cast term, typ) sigma x
          in
          fold fold_subpattern pat sigma x
        | BoundPattern.Var z, typ ->
          begin
            match VarTable.find_opt z sigma with
            | Some term -> g term sigma x (* TODO check type. [typ] may missmatch the type of [term]. *)
            | None ->
              begin
                let fold_type_inhabitant term x =
                  let sigma = VarTable.set z term sigma in
                  g term sigma x
                in
                fold_type_inhabitants ~epsilon fold_type_inhabitant typ t x
              end
          end
       in
       fold (fun term _ x -> g term x) pattern (VarTable.create 8) x *)

    (* TODO use fold_pattern_instances to replace this implementation. *)
    let instanciate_pattern_opt ?(epsilon=true) conf t =
      let table = Hashtbl.create 8 in
      let rec instanciate conf =
        match conf with
        | BoundPattern.Cons (f, l), typ ->
          begin
            match list_map_opt instanciate l with
            | Some l -> Some (BoundTerm.Term (f, l), typ)
            | None -> None
          end
        | BoundPattern.Cast conf, typ ->
          begin
            match instanciate conf with
            | Some term -> Some (BoundTerm.Cast term, typ)
            | None -> None
          end
        | BoundPattern.Var x, typ ->
          begin
            match Hashtbl.find_opt table x with
            | Some term -> Some term (* TODO check type. [typ] may missmatch the type of [term]. *)
            | None ->
              begin
                match pick_binding_inhabitant_opt ~epsilon typ t with
                | Some term ->
                  Hashtbl.add table x term;
                  Some term
                | None -> None
              end
          end
      in
      instanciate conf

    let rec recognizes_bound_pattern_in_conf ?(debug=false) ?(epsilon=true) (conf, (q, label)) (pattern, (typ_q, typ_label)) t =
      let recognizes typed_conf bound_pattern =
        recognizes_bound_pattern_in_conf ~debug ~epsilon typed_conf bound_pattern t
      in
      let concrete a = function
        | Some a -> a
        | None -> a
      in
      let try_state q' =
        (* if debug then
           begin
            debug_print "for ";
            BoundConfiguration.format ppf (conf, (q, label));
            debug_print "   with   ";
            BoundPattern.format ppf (pattern, (typ_q, typ_label));
            debug_print "\ntry state: ";
            State.format ppf q';
            debug_print "\n"
           end; *)
        match conf, pattern with
        | _, BoundPattern.Var _ ->
          begin
            match instanciate_typed_configuration_opt ~epsilon (conf, (q, label)) t with
            | Some _ -> true
            | None -> false
          end
        | BoundConfiguration.Cast typed_conf, BoundPattern.Cast bound_pattern ->
          recognizes typed_conf bound_pattern
        | BoundConfiguration.Cons (f1, l1), BoundPattern.Cons (f2, l2) when Sym.equal f1 f2 ->
          List.for_all2 recognizes l1 l2
        | BoundConfiguration.Var _, _ ->
          let confs = configurations_for_state q' t in
          let fold_conf (conf', label') = function
            | true -> true
            | false ->
              begin
                match conf' with
                | Configuration.Var _ -> false
                | _ ->
                  let label_checked = label_typecheck label' typ_label in
                  (* if not label_checked then debug_print "label typecheck failed.\n"; *)
                  label_checked &&
                  recognizes (typed_transition conf' (concrete label' label) (concrete q' q)) (pattern, (typ_q, typ_label))
              end
          in
          LabeledConfigurationSet.fold fold_conf confs false
        | _ -> false
      in
      let recognizes_in q =
        if epsilon then
          let fold_state q' = function
            | true -> true
            | false ->
              let r = try_state q' in
              (* if r && debug then
                 debug_print "found!\n"; *)
              r
          in
          fold_epsilon_class_type fold_state q typ_q t false
        else
          begin
            if state_typecheck q typ_q then
              try_state q
            else
              false
          end
      in
      match q with
      | Some q -> recognizes_in q
      | None ->
        let fold_state q = function
          | true -> true
          | false -> recognizes_in q
        in
        fold_states fold_state t false

    let recognizes_bound_pattern_in ?(debug=false) ?(epsilon=true) q bound_pattern t =
      recognizes_bound_pattern_in_conf ~debug ~epsilon (BoundConfiguration.Var (Var.of_int 0), (Some q, None)) bound_pattern t

    let recognizes_bound_pattern  ?(epsilon=true) pattern t =
      StateSet.exists (function q -> recognizes_bound_pattern_in ~epsilon q pattern t) (final_states t)
  end
end

module Make (F : Symbol.S) (Q : STATE) (L : LABEL) = struct
  module Base = MakeBase (F) (Q) (L)
  include Extend (Base)

  let empty = Base.empty
end

module MakeStateOption (Q : STATE) = struct
  type t = Q.t option

  let product q1 q2 =
    match q1, q2 with
    | Some q1, Some q2 ->
      if Q.compare q1 q2 = 0 then
        Some (Some q1)
      else
        None
    | Some q1, _ -> Some (Some q1)
    | _, Some q2 -> Some (Some q2)
    | _, _ -> Some None

  let compare q1 q2 =
    match q1, q2 with
    | Some q1, Some q2 -> Q.compare q1 q2
    | Some _, None -> 1
    | None, Some _ -> -1
    | None, None -> 0

  let equal q1 q2 =
    match q1, q2 with
    | Some q1, Some q2 -> Q.equal q1 q2
    | None, None -> true
    | _, _ -> false

  let hash = Hashtbl.hash

  let print t out =
    match t with
    | Some q ->
      (*				Format.pp_print_string ppf ":";*)
      Q.print q out
    | None ->
      Format.fprintf out "~"
end

module MakeStateProduct (A : STATE) (B : STATE) = struct
  type t = A.t * B.t

  let product (a1, b1) (a2, b2) =
    match A.product a1 a2, B.product b1 b2 with
    | Some a, Some b -> Some (a, b)
    | _, _ -> None

  let compare (a1, b1) (a2, b2) =
    let c = A.compare a1 a2 in
    if c = 0 then B.compare b1 b2 else c

  let equal (a1, b1) (a2, b2) =
    A.equal a1 a2 && B.equal b1 b2

  let hash (a, b) =
    (A.hash a) lxor (B.hash b)

  let print (a, b) out =
    Format.fprintf out "%t.%t" (A.print a) (B.print b)
end

module Ext (A : S) (B : S with module Sym = A.Sym) = struct
  module ExtConf = Pattern.Ext (A.Configuration) (B.Configuration)
  module ExtLabeledConfSet = Set.Ext (A.LabeledConfigurationSet) (B.LabeledConfigurationSet)
  module ExtLabeledStateSet = Set.Ext (A.LabeledStateSet) (B.LabeledStateSet)
  module ExtConfSet = Set.Ext (A.ConfigurationSet) (B.ConfigurationSet)
  module ExtStateSet = Set.Ext (A.StateSet) (B.StateSet)
  module ExtConfMap = Map.Ext (A.ConfigurationMap) (B.ConfigurationMap)
  module ExtStateMap = Map.Ext (A.StateMap) (B.StateMap)

  module StatePair = MakeStateProduct (A.State) (B.State)
  module StatePairSet = Set.Make (StatePair)

  (*		roots : StateSet.t; (* Final states. *)*)
  (*		state_confs : LabeledConfigurationSet.t StateMap.t; (* Associates to each state the set of configurations leading to it. *)*)
  (*		conf_states : LabeledStateSet.t ConfigurationMap.t; (* Associates to each configuration the set of states to go to. *)*)
  (*		state_parents : ConfigurationSet.t StateMap.t *)

  let map ?filter f_data f_label f_state a =
    let map_label = Hashtbl.create 8 in (* 8: arbitrary size *)
    let map_state = Hashtbl.create 8 in (* 8: arbitrary size *)
    let f_label = find_or_create (f_label) map_label in
    let f_state = find_or_create (f_state) map_state in
    let rec f_conf = function
      | A.Configuration.Cons (f, l) -> B.Configuration.Cons (f, (List.map (f_conf) l))
      | A.Configuration.Var q -> B.Configuration.Var (f_state q)
    in
    (* let f_labeled_state (q, label) = (f_state q, f_label label) in
       let f_labeled_conf (conf, label) = (f_conf conf, f_label label) in
       let f_labeled_states set = ExtLabeledStateSet.map (f_labeled_state) set in
       let f_labeled_confs set = ExtLabeledConfSet.map (f_labeled_conf) set in
       let f_conf_labeled_states conf set = (f_conf conf, f_labeled_states set) in
       let f_state_labeled_confs q set = (f_state q, f_labeled_confs set) in
       let f_labeled_states_union set1 set2 = Some (B.LabeledStateSet.union set1 set2) in
       let f_labeled_confs_union set1 set2 = Some (B.LabeledConfigurationSet.union set1 set2) in
       let f_confs set = ExtConfSet.map (f_conf) set in
       let f_confs_union set1 set2 = Some (B.ConfigurationSet.union set1 set2) in
       let f_parent q confs = (f_state q, f_confs confs) in *)

    let add conf label q b =
      if match filter with
        | Some f -> f conf label q
        | None -> true
      then B.add_transition (f_conf conf) (f_label label) (f_state q) b
      else b
    in
    let aut = A.fold_transitions add a (B.create (f_data (A.data a))) in
    let add_final q b =
      B.add_final_state (f_state q) b
    in
    A.StateSet.fold add_final (A.final_states a) aut

  (* {
     B.roots = ExtStateSet.map (f_state) a.A.roots;
     B.state_confs = ExtStateMap.map (f_state_labeled_confs) (f_labeled_confs_union) a.A.state_confs;
     B.conf_states = ExtConfMap.map (f_conf_labeled_states) (f_labeled_states_union) a.A.conf_states;
     B.state_parents = ExtStateMap.map (f_parent) (f_confs_union) a.A.state_parents
     } *)

  let states_intersection_opt qa qb a b =
    let exception Found of A.BoundTerm.t * B.BoundTerm.t in
    let rec states_intersection' visited qa qb =
      if StatePairSet.mem (qa, qb) visited then
        None
      else
        begin
          let visited = StatePairSet.add (qa, qb) visited in
          let qa_confs = A.configurations_for_state qa a in
          let qb_confs = B.configurations_for_state qb b in
          try
            A.LabeledConfigurationSet.iter ( (* exists *)
              function qa_conf, label_a ->
                B.LabeledConfigurationSet.iter ( (* exists *)
                  function qb_conf, label_b ->
                  match qa_conf, qb_conf with
                  | A.Configuration.Cons (fa, la), B.Configuration.Cons (fb, lb) when A.Sym.equal fa fb ->
                    begin match List.map2_opt
                                  (states_intersection' visited)
                                  (List.map A.Configuration.normalized la)
                                  (List.map B.Configuration.normalized lb) with
                    | Some ll ->
                      let la, lb = List.split ll in
                      let ta = A.BoundTerm.Term (fa, la), (Some qa, Some label_a) in
                      let tb = B.BoundTerm.Term (fb, lb), (Some qb, Some label_b) in
                      raise (Found (ta, tb))
                    | None -> ()
                    end
                  | A.Configuration.Var qa', B.Configuration.Var qb' ->
                    begin match states_intersection' visited qa' qb' with
                      | Some (ta, tb) ->
                        let ta = A.BoundTerm.Cast ta, (Some qa, Some label_a) in
                        let tb = B.BoundTerm.Cast tb, (Some qb, Some label_b) in
                        raise (Found (ta, tb))
                      | None -> ()
                    end
                  | _ ->
                    ()
                ) qb_confs;
            ) qa_confs;
            (* epsilon transitions in a *)
            A.LabeledConfigurationSet.iter (
              function qa_conf, label_a ->
              match qa_conf with
              | A.Configuration.Var qa' ->
                begin match states_intersection' visited qa' qb with
                  | Some (ta, tb) ->
                    let ta = A.BoundTerm.Cast ta, (Some qa, Some label_a) in
                    raise (Found (ta, tb))
                  | None -> ()
                end
              | _ -> ()
            ) qa_confs;
            (* epsilon transitions in b *)
            B.LabeledConfigurationSet.iter (
              function qb_conf, label_b ->
              match qb_conf with
              | B.Configuration.Var qb' ->
                begin match states_intersection' visited qa qb' with
                  | Some (ta, tb) ->
                    let tb = B.BoundTerm.Cast tb, (Some qb, Some label_b) in
                    raise (Found (ta, tb))
                  | None -> ()
                end
              | _ -> ()
            ) qb_confs;
            None
          with
          | Found (a, b) -> Some (a, b)
        end
    in
    states_intersection' StatePairSet.empty qa qb

  let states_intersects qa qb a b =
    Option.is_some (states_intersection_opt qa qb a b)

  let state_included_in ?(epsilon=true) a b qa qb : B.BoundTerm.t option =
    let rec state_included_in' visited qa qb : B.BoundTerm.t option =
      if StatePairSet.mem (qa, qb) visited then
        None
      else
        begin
          let visited = StatePairSet.add (qa, qb) visited in
          let qb_confs = B.configurations_for_state qb b in
          let qa_confs = A.configurations_for_state qa a in
          (* Check that for all configuration of [qb] there exists an equivalent configuration in [qa] *)
          B.LabeledConfigurationSet.fold (
            function b_conf -> function
              | Some sample -> Some sample
              | None ->
                begin match b_conf with
                  | B.Configuration.Cons (fb, lb), label ->
                    let lb = List.map B.Configuration.normalized lb in
                    (* Check if there exists an exquivalent configuration in [qa]. *)
                    let included, samples = A.LabeledConfigurationSet.fold (
                        function a_conf -> function
                          | true, samples -> true, samples
                          | false, samples ->
                            begin match a_conf with
                              | A.Configuration.Cons (fa, la), _ when A.Sym.equal fa fb ->
                                begin
                                  (* Check that for all sub-states of lb, it is included in the quivalent state in la. *)
                                  List.fold_right2
                                    (
                                      fun qa' qb' (included, samples) ->
                                        if included then
                                          match state_included_in' visited qa' qb' with
                                          | None -> (included, None::samples)
                                          | Some sample -> (false, (Some sample)::samples)
                                        else (false, None::samples)
                                    )
                                    (List.map A.Configuration.normalized la)
                                    lb
                                    (true, [])
                                end
                              | _ ->
                                false, samples
                            end
                      ) qa_confs (false, List.init (List.length lb) (function _ -> None))
                    in
                    if included then begin
                      None
                    end else begin
                      let samples = List.map2
                          (
                            function qb' -> function
                              | Some sample -> sample
                              | None -> B.pick_term_in qb' b
                          )
                          lb samples
                      in
                      Some (B.BoundTerm.Term (fb, samples), (Some qb, Some label))
                    end
                  | B.Configuration.Var _, _ when not epsilon ->
                    None
                  | B.Configuration.Var qb', label ->
                    begin match state_included_in' visited qa qb' with
                      | Some sample -> Some (B.BoundTerm.Cast sample, (Some qb', Some label))
                      | None -> None
                    end
                end
          ) qb_confs None
        end
    in
    match state_included_in' StatePairSet.empty qa qb with
    | Some sample ->
      (* Log.debug "state %t is not included in %t because of \n%t\n@."
         (B.State.print qb) (A.State.print qa) (B.BoundTerm.print sample); *)
      Some sample
    | None -> None

  type renaming = A.State.t B.StateMap.t

  exception Found of renaming

  let rec state_renaming ?(epsilon=true) ?(knowledge=B.StateMap.empty) label_eq a b qa qb =
    match B.StateMap.find_opt qb knowledge with
    | Some q when A.State.equal qa q -> Some knowledge
    | Some _ -> None
    | None ->
      begin
        (* NOTE idea: Use MurmurHash to hash the structure of each state. *)
        let match_confs (qa_conf, qa_label) (qb_conf, qb_label) knowledge =
          if label_eq qa_label qb_label then
            match qa_conf, qb_conf with
            | A.Configuration.Cons (fa, la), B.Configuration.Cons (fb, lb) when A.Sym.equal fa fb ->
              begin
                try
                  let knowledge = List.fold_right2 (
                      fun qa' qb' knowledge ->
                        match state_renaming ~epsilon ~knowledge label_eq a b qa' qb' with
                        | Some knowledge -> knowledge
                        | None -> raise Not_found
                    ) (List.map A.Configuration.normalized la) (List.map B.Configuration.normalized lb) knowledge
                  in
                  Some knowledge
                with
                | Not_found -> None
              end
            | A.Configuration.Var qa', B.Configuration.Var qb' ->
              state_renaming ~epsilon ~knowledge label_eq a b qa' qb'
            | _ -> None
          else
            None
        in
        try
          let remove_epsilons_a confs =
            if epsilon then confs else
              A.LabeledConfigurationSet.filter (
                function
                | A.Configuration.Var _, _ -> false
                | _ -> true
              ) confs
          in
          let remove_epsilons_b confs =
            if epsilon then confs else
              B.LabeledConfigurationSet.filter (
                function
                | B.Configuration.Var _, _ -> false
                | _ -> true
              ) confs
          in
          let qa_confs = remove_epsilons_a (A.configurations_for_state qa a) in
          let qb_confs = remove_epsilons_b (B.configurations_for_state qb b) in
          if A.LabeledConfigurationSet.cardinal qa_confs = B.LabeledConfigurationSet.cardinal qb_confs then
            try
              let rec find_renaming qa_confs qb_confs knowledge =
                if A.LabeledConfigurationSet.is_empty qa_confs then
                  raise (Found knowledge)
                else
                  begin
                    let qa_conf = A.LabeledConfigurationSet.choose qa_confs in
                    B.LabeledConfigurationSet.iter (
                      function qb_conf ->
                      match match_confs qa_conf qb_conf knowledge with
                      | Some knowledge ->
                        begin
                          let qa_confs = A.LabeledConfigurationSet.remove qa_conf qa_confs in
                          let qb_confs = B.LabeledConfigurationSet.remove qb_conf qb_confs in
                          try find_renaming qa_confs qb_confs knowledge with
                          | Not_found -> ()
                        end
                      | None -> ()
                    ) qb_confs;
                    raise Not_found
                  end
              in
              find_renaming qa_confs qb_confs (B.StateMap.add qb qa knowledge);
              None
            with
            | Found knowledge -> Some knowledge
          else
            raise Not_found
        with
        | Not_found -> None
      end
end

module Product (A : S) (B : S with module Sym = A.Sym) (AB : S with module Sym = B.Sym) = struct
  module ConfProduct = Pattern.Product (A.Configuration) (B.Configuration) (AB.Configuration)
  module ExtLabeledConfSet = Set.Ext (A.LabeledConfigurationSet) (B.LabeledConfigurationSet)
  module ExtStateMap = Map.Ext (A.StateMap) (B.StateMap)
  module ExtStateSet = Set.Ext (A.StateSet) (B.StateSet)

  let do_product ?hook epsilon label_product state_product aut a b_state_confs b_roots =
    let product qa qa_confs qb qb_confs aut =
      match state_product qa qb with
      | Some q ->
        let conf_product (ca, la) (cb, lb) aut =
          match (ConfProduct.product (state_product) ca cb), (label_product la lb) with
          | Some conf, Some label ->
            AB.add_transition conf label q aut
          | None, Some label ->
            if epsilon then
              begin (* this part handles epsilon transitions. *)
                match ca, cb with
                | A.Configuration.Var qa', _ ->
                  begin
                    match state_product qa' qb with
                    | Some q' ->
                      AB.add_transition (AB.Configuration.Var q') label q aut
                    | None -> aut
                  end
                | _, B.Configuration.Var qb' ->
                  begin
                    match state_product qa qb' with
                    | Some q' ->
                      AB.add_transition (AB.Configuration.Var q') label q aut
                    | None -> aut
                  end
                | _, _ -> aut
              end
            else aut
          | _, None -> aut
        in
        let aut = ExtLabeledConfSet.fold2 (conf_product) (qa_confs) (qb_confs) aut in
        begin
          match hook with
          | Some h -> h aut q
          | None -> ()
        end;
        aut
      | None -> aut
    in
    let add_final qa qb aut =
      match state_product qa qb with
      | Some q -> AB.add_final_state q aut
      | None -> aut
    in
    let aut = ExtStateMap.fold2 product (A.configurations_for_states a) b_state_confs aut in
    ExtStateSet.fold2 add_final (A.final_states a) b_roots aut

  let product ?hook ?(epsilon=true) data_product label_product state_product a b =
    (*		let map = Hashtbl.create 8 in (* 8: arbitrary size *)*)
    (*		let state_product a b = find_or_create (function (a, b) -> product a b) map (a, b) in*)
    do_product ?hook epsilon label_product state_product (AB.create (data_product (A.data a) (B.data b))) a (B.configurations_for_states b) (B.final_states b)
end
