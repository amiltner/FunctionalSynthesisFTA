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
  module StateSet : MyStdLib.HashSet.ImperativeSet with type elt = State.t
  module StateMap : MyStdLib.HashTable.ImperativeDict with type key = State.t
  module ConfigurationSet : MyStdLib.HashSet.ImperativeSet with type elt = Configuration.t
  module ConfigurationMap : Map.S with type key = Configuration.t
  module LabeledConfigurationSet : Set.S with type elt = LabeledConfiguration.t
  module LabeledStateSet : Set.S with type elt = LabeledState.t
  type t
  type data
  val create : data -> t
  val empty : unit -> t
  val data : t -> data
  val clear : t -> t
  val copy : t -> t
  val final_states : t -> StateSet.t
  val configurations_for_states : t -> LabeledConfigurationSet.t StateMap.t
  val states_for_configurations : t -> LabeledStateSet.t ConfigurationMap.t
  val state_parents : State.t -> t -> ConfigurationSet.t
  val add_final_state : State.t -> t -> unit
  val add_final_states : StateSet.t -> t -> unit
  val set_final_states : StateSet.t -> t -> unit
  type hook = Configuration.t -> Label.t -> State.t -> unit
  val add_transition : ?hook:hook -> Configuration.t -> Label.t -> State.t -> t -> unit
  val add_transition_unchecked : Configuration.t -> Label.t -> State.t -> t -> unit
  val remove_transition : Configuration.t -> Label.t -> State.t -> t -> unit
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
  val map : ?filter:(Configuration.t -> Label.t -> State.t -> t -> bool) -> (Label.t -> Label.t) -> (State.t -> State.t) -> t -> t
  val filter : (Configuration.t -> Label.t -> State.t -> bool) -> t -> t
  val fold_states : (State.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_transitions : (Configuration.t -> Label.t -> State.t -> 'a -> 'a) -> t -> 'a -> 'a
  val label : ((State.t -> 'a) -> State.t -> 'a) -> (State.t -> 'a) -> t -> (State.t -> 'a)
  val inter : ?hook:(t -> State.t -> unit) -> (data -> data -> data) -> t -> t -> t
  val reachable_states : ?epsilon:bool -> t -> StateSet.t
  val reachable_values : t -> BoundTerm.t StateMap.t
  val reduce : ?epsilon:bool -> ?from_finals:bool -> t -> t
  val unepsilon : t -> t
  val prune_useless : t -> t
  type renaming = State.t StateMap.t
  type normalizer = Sym.t -> State.t list -> LabeledState.t
  val print : t -> Format.formatter -> unit
  module Patterns (Var : Pattern.VARIABLE) : sig
    type pattern = (Sym.t, Var.t) Pattern.pattern
    val recognizes_pattern_in : State.t -> pattern -> t -> bool
    val configuration_of_pattern : (Var.t -> State.t) -> pattern -> Configuration.t
  end
  type dynamic_filter =
    | NoFilter
    | Filter of (State.t -> Label.t -> (bool * dynamic_filter))
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
    [@@deriving hash]

    let compare (a, la) (b, lb) =
      let c = Label.compare la lb in
      if c = 0 then Configuration.compare a b else c

    let print (c, l) out =
      Configuration.print c out;
      Label.print l out

    let equal (a,la) (b,lb) =
      (Label.equal la lb) && (Configuration.equal a b)
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

  module StateP = struct
    include State

    let pp _ _ = failwith "no"
    let show _ = failwith "no"
  end

  module ConfigurationP = struct
    include Configuration

    let pp _ _ = failwith "no"
    let show _ = failwith "no"
  end

  module StateSet = MyStdLib.HashSet.HSWrapper (StateP)
  module StateMap = MyStdLib.HashTable.Make(StateP)

  module ConfigurationSet = MyStdLib.HashSet.HSWrapper (ConfigurationP)
  module ConfigurationMap = Map.Make (Configuration)

  module LabeledStateSet = Set.Make (LabeledState)
  module LabeledConfigurationSet = Set.Make (LabeledConfiguration)

  type t = {
    mutable roots : StateSet.t; (* Final states. *)
    mutable state_confs : LabeledConfigurationSet.t StateMap.t; (* Associates to each state the set of configurations leading to it. *)
    mutable conf_states : LabeledStateSet.t ConfigurationMap.t; (* Associates to each configuration the set of states to go to. *)
    mutable state_parents : ConfigurationSet.t StateMap.t (* Associates to each state the set of configurations it appears in. *)
  }

  type data = unit

  let empty () = {
    roots = (StateSet.empty ());
    state_confs = StateMap.empty ();
    conf_states = ConfigurationMap.empty;
    state_parents = StateMap.empty () ;
  }

  let create _ = empty ()

  let data _ = ()

  let clear _ = empty ()

  let copy x = x

  let final_states a = a.roots

  let configurations_for_states a =
    a.state_confs

  let states_for_configurations a =
    a.conf_states

  let state_parents q a =
    match StateMap.find_opt q a.state_parents with
    | Some set -> set
    | None ->
      let p = (ConfigurationSet.empty ()) in
      StateMap.add q p a.state_parents;
      p

  let add_final_state q a =
    StateSet.add q a.roots

  let add_final_states set a =
    StateSet.iter
      (fun e -> StateSet.add e a.roots)
      set

  let set_final_states set a =
    a.roots <- set

  type hook = Configuration.t -> Label.t -> State.t -> unit

  let configurations_for_state q a =
    match StateMap.find_opt q a.state_confs with
    | Some set -> set
    | None -> (LabeledConfigurationSet.empty)

  let states_for_configuration conf a =
    match ConfigurationMap.find_opt conf a.conf_states with
    | Some set -> set
    | None -> (LabeledStateSet.empty)

  let add_transition ?hook conf label q (a:t) =
    let add_parent_to q () =
      let cs = (state_parents q a) in
      (ConfigurationSet.add conf cs)
    in
    StateMap.add q (LabeledConfigurationSet.add (conf, label) (configurations_for_state q a)) a.state_confs;
    a.conf_states <- ConfigurationMap.add conf (LabeledStateSet.add (q, label) (states_for_configuration conf a)) a.conf_states;
    Configuration.fold add_parent_to conf ()

  let add_transition_unchecked conf label q (a:t) =
    let add_parent_to q () =
      let cs = (state_parents q a) in
      (ConfigurationSet.add conf cs);
    in
    StateMap.add q (LabeledConfigurationSet.add (conf, label) (configurations_for_state q a)) a.state_confs;
    a.conf_states <- ConfigurationMap.add conf (LabeledStateSet.add (q, label) (states_for_configuration conf a)) a.conf_states;
    Configuration.fold add_parent_to conf ()

  let remove_transition conf label q (a:t) =
    let remove_parent_from q () =
      let cs = (state_parents q a) in
      (ConfigurationSet.remove conf cs);
    in
    StateMap.add q (LabeledConfigurationSet.remove (conf, label) (configurations_for_state q a)) a.state_confs;
    a.conf_states <- ConfigurationMap.add conf (LabeledStateSet.remove (q, label) (states_for_configuration conf a)) a.conf_states;
    Configuration.fold remove_parent_from conf ()
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
    let hash_fold_option = MyStdLib.hash_fold_option
    type t = State.t option * Label.t option
    [@@deriving hash]

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
    | None ->
      LabeledConfigurationSet.empty

  let is_state_empty q a =
    let confs = configurations_for_state q a in
    LabeledConfigurationSet.is_empty confs

  let states_for_configuration conf a =
    match ConfigurationMap.find_opt conf (states_for_configurations a) with
    | Some set -> set
    | None -> LabeledStateSet.empty

  let sub_states_of a q =
    let sub_states = StateSet.empty () in
    let confs = configurations_for_state q a in
    LabeledConfigurationSet.fold (
      fun (conf, _) () ->
        match Configuration.node conf with
        | Configuration.Var q' ->
          StateSet.add q' sub_states
        | _ -> ()
    ) confs ()

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
      match Configuration.node conf with
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
    let set = ConfigurationSet.empty () in
    let visited = Hashtbl.create 8 in
    let rec fold_state q () =
      match Hashtbl.find_opt visited q with
      | Some () -> ()
      | None ->
        Hashtbl.add visited q ();
        let fold_conf conf () =
          match Configuration.node conf with
          | Configuration.Var _ -> fold_state q ()
          | _ -> ConfigurationSet.add conf set
        in
        ConfigurationSet.fold fold_conf (state_parents q a) ()
    in
    fold_state q ();
    set

  let fold_transitions f a x =
    let fold_state_confs q confs x =
      let fold_labeled_confs (conf, label) = f conf label q in
      LabeledConfigurationSet.fold (fold_labeled_confs) confs x
    in
    StateMap.fold (fold_state_confs) (configurations_for_states a) x

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
      fold_configuration (Configuration.node conf)
    and fold_configuration conf x =
      match conf with
      | Configuration.Cons (_, l) -> List.fold_right (fold_configuration) l x
      | Configuration.Var q -> fold_state q x
    and fold_transition conf _ q x =
      fold_configuration (Configuration.node conf) (uniq_f q x)
    in
    let x = StateSet.fold (uniq_f) (final_states a) x in
    fold_transitions (fold_transition) a x

  let states a =
    let ss = StateSet.empty () in
    fold_states (fun x () -> StateSet.add x ss) a ();
    ss

  let is_final a q =
    StateSet.contains q (final_states a)

  let state_count a =
    fold_states (fun _ k -> k + 1) a 0

  let mem conf label state a =
    let states = states_for_configuration conf a in
    LabeledStateSet.mem (state, label) states

  let mem_configuration conf a =
    begin match ConfigurationMap.find_opt conf (states_for_configurations a) with
      | Some _ -> true
      | None -> false
    end

  let mem_state q a =
    begin match StateMap.find_opt q (configurations_for_states a) with
      | None -> false
      | Some _ -> true
    end || StateSet.contains q (final_states a)

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
          match Configuration.node conf with
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
              match Configuration.node conf with
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
              match Configuration.node conf with
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
              match Configuration.node conf with
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
                match Configuration.node conf with
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
    List.exists (function q -> recognizes_in q term t) (StateSet.as_list (final_states t))

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

  let filter p t =
    let aut = empty () in
    let add conf label q () =
      if p conf label q then
        add_transition_unchecked conf label q aut
      else
        ()
    in
    fold_transitions add t ();
    let add_final q =
      add_final_state q aut
    in
    StateSet.iter add_final (final_states t);
    aut


  let sub_automaton states t =
    let u = empty () in
    let visited = Hashtbl.create 8 in
    let rec visit_state q () =
      match Hashtbl.find_opt visited q with
      | Some () -> ()
      | None ->
        Hashtbl.add visited q ();
        let confs = configurations_for_state q t in
        let add_conf (conf, label) () =
          let u = add_transition conf label q u in
          visit_conf conf u
        in
        LabeledConfigurationSet.fold add_conf confs ()
    and visit_conf_internal conf () =
      match conf with
      | Configuration.Cons (_, l) ->
        List.fold_right visit_conf_internal l ()
      | Configuration.Var q ->
        visit_state q ()
    and visit_conf x u = visit_conf_internal (Configuration.node x) ()
    in
    (set_final_states states u);
    StateSet.fold visit_state states ();
    u

  let inter ?hook data_product a b =
    let aut = empty () in
    (*		let map = Hashtbl.create 8 in (* 8: arbitrary size *)*)
    (*		let state_product a b = find_or_create (function (a, b) -> State.product a b) map (a, b) in*)
    let product qa qa_confs qb qb_confs () =
      match State.product qa qb with
      | Some q ->
        let labeled_conf_product (ca, la) (cb, lb) () =
            match (Configuration.product ca cb), (Label.product la lb) with
            | Some conf, Some label -> add_transition conf label q aut
            | None, Some label ->
              begin
                match Configuration.node ca, Configuration.node cb with
                | Configuration.Var qa', _ ->
                  begin
                    match State.product qa' qb with
                    | Some q' -> add_transition (Configuration.of_var q') label q aut
                    | None -> ()
                  end
                | _, Configuration.Var qb' ->
                  begin
                    match State.product qa qb' with
                    | Some q' -> add_transition (Configuration.of_var q') label q aut
                    | None -> ()
                  end
                | _, _ -> ()
              end
            | _, None -> ()
          in
          LabeledConfigurationSet.fold2 (labeled_conf_product) (qa_confs) (qb_confs) ();
          begin
            match hook with
            | Some h -> h aut q
            | None -> ()
          end;
          ()
        | None -> ()
      in
      let add_final qa qb () =
        match State.product qa qb with
        | Some q -> add_final_state q aut
        | None -> ()
      in
      StateMap.fold2 product (configurations_for_states a) (configurations_for_states b) ();
      StateSet.fold2 add_final (final_states a) (final_states b) ();
      aut

  let reachable_states ?(epsilon=true) a =
    let visited = Hashtbl.create 8 in
    let reachable set c = StateSet.contains c set in
    let set = StateSet.empty () in
    let rec reach_conf conf set =
      reach_conf_states conf (states_for_configuration conf a) set
    and reach_conf_states conf lbl_states () =
      let fold (q, _) () =
        match Hashtbl.find_opt visited q with
        | Some () -> ()
        | None ->
          Hashtbl.add visited q ();
          ConfigurationSet.fold (reach_conf) (state_parents q a) (StateSet.add q set)
      in
      if (epsilon || Configuration.is_cons conf) && (Configuration.for_all (reachable set) conf) then
        LabeledStateSet.fold (fold) lbl_states ()
      else ()
    in
    ConfigurationMap.fold (reach_conf_states) ((states_for_configurations a)) ();
    set

  let reduce ?(epsilon=true) ?(from_finals=true) t =
    let rt = empty () in
    let reachable_states = reachable_states ~epsilon t in
    let is_reachable_state q = StateSet.contains q reachable_states in
    let is_reachable_conf = Configuration.for_all is_reachable_state in
    let for_each_transition conf label q () =
      if is_reachable_state q && is_reachable_conf conf then
        add_transition conf label q rt
      else
        ()
    in
    fold_transitions for_each_transition t ();
    let for_each_final_state q () =
      if is_reachable_state q then
        add_final_state q rt
      else ()
    in
    (if from_finals then
      StateSet.fold for_each_final_state (final_states t) ()
    else
      fold_states for_each_final_state t ());
    rt

  let alphabet t =
    let rec fold_conf conf alphabet =
      match conf with
      | Configuration.Cons (f, l) ->
        List.fold_right fold_conf l (SymSet.add f alphabet)
      | Configuration.Var _ -> alphabet
    in
    let fold_transition conf _ _ alphabet =
      fold_conf (Configuration.node conf) alphabet
    in
    fold_transitions fold_transition t (SymSet.empty)


  let unepsilon _ =
    failwith "TODO: unepsilon: Not implemented yet."

  let prune_useless (x:t)
    : t =
    let x = reduce x in
    let fs = final_states x in
      let x = sub_automaton fs x in
    x

  type renaming = State.t StateMap.t

  exception Found of renaming

  let print t out =
    let print_state_confs q confs =
      let print_conf conf =
        Format.fprintf out "%t -> %t\n" (LabeledConfiguration.print conf) (State.print q)
      in
      LabeledConfigurationSet.iter (print_conf) confs
    and print_state q =
      Format.fprintf out "%t " (State.print q)
    in
    Format.fprintf out "States ";
    StateSet.iter print_state (states t);
    Format.fprintf out "\n\nFinal States ";
    StateSet.iter print_state (final_states t);
    Format.fprintf out "\n\nTransitions\n";
    StateMap.iter print_state_confs (configurations_for_states t)

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
                    match Configuration.node conf with
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

    (*let recognizes_pattern pattern t =
      StateSet.exists (function q -> recognizes_pattern_in q pattern t) (final_states t)*)

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
                match Configuration.node conf with
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
                match Configuration.node conf with
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
              match Configuration.node conf with
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

  let rec config_to_bt_opt
      (f:State.t -> BoundTerm.t option)
      (c:Configuration.t_node)
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
  let config_to_bt_opt f c = config_to_bt_opt f (Configuration.node c)

  let reachable_values a =
    let map = (StateMap.empty ()) in
    let retrieve_computed_value map c = StateMap.find_opt c map in
    let rec find_reachables todos =
      begin match todos with
        | [] -> map
        | (config,lbl_states)::todos ->
          let bto = config_to_bt_opt (retrieve_computed_value map) config in
          begin match bto with
            | None -> find_reachables todos
            | Some bt ->
              let (new_todos) =
                LabeledStateSet.fold
                  (fun (q,_) new_todos ->
                     begin match StateMap.find_opt q map with
                       | Some _ -> new_todos
                       | None ->
                       StateMap.add q bt map;
                       let new_todos =
                         ConfigurationSet.fold
                           (fun c new_todos ->
                              (c,states_for_configuration c a)::new_todos)
                           (state_parents q a)
                           new_todos
                       in
                       new_todos
                     end)
                  lbl_states
                  []
              in
              find_reachables (todos@new_todos)
          end
      end
    in
    let initial_todos =
      ConfigurationMap.fold
        (fun c lbl_states acc -> (c,lbl_states)::acc)
        (states_for_configurations a)
        []
    in
    find_reachables initial_todos

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
                        match Configuration.node conf with
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
end

module Make (F : Symbol.S) (Q : STATE) (L : LABEL) = struct
  module Base = MakeBase (F) (Q) (L)
  include Extend (Base)

  let empty = Base.empty

  let compare x y = 0
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
