(** Tree Automata.

*)

open Collections

module type STATE = Pattern.VARIABLE
module type LABEL = Pattern.VARIABLE
module type TYPE = TypedTerm.TYPE

module type BASE = sig
  (** Terms *)
  module Sym : Symbol.S
  module State : STATE
  module Label : LABEL

  (** Non normalised configurations.
      Note that all configurations in the automaton are normalised. *)
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

  (** Sets of states. *)
  module StateSet : Set.S with type elt = State.t

  module StateMap : Map.S with type key = State.t

  (** Set of configurations. *)
  module ConfigurationSet : Set.S with type elt = Configuration.t

  module ConfigurationMap : Map.S with type key = Configuration.t

  (** Set of labeled configurations. *)
  module LabeledConfigurationSet : Set.S with type elt = LabeledConfiguration.t

  module LabeledStateSet : Set.S with type elt = LabeledState.t

  (** The type of automata. *)
  type t

  type data

  (** The empty automaton. *)
  val create : data -> t

  val data : t -> data

  val clear : t -> t

  (** Returns the final states of the automaton. *)
  val final_states : t -> StateSet.t

  (** Returns a map associating each state to the set of configuration generating it. *)
  val configurations_for_states : t -> LabeledConfigurationSet.t StateMap.t

  (** Returns a map associating each configuration to the set of states generated by it. *)
  val states_for_configurations : t -> LabeledStateSet.t ConfigurationMap.t

  (** Find all configuration using this state.
      This also includes epsilon transitions/configurations.
      Complexity O(log(n)). *)
  val state_parents : State.t -> t -> ConfigurationSet.t

  val add_final_state : State.t -> t -> t
  (** Add a final state. *)

  val add_final_states : StateSet.t -> t -> t
  (** Add multiple final states. *)

  val set_final_states : StateSet.t -> t -> t

  (** A hook is called when a new transition is added to the automaton in 'add_configuration'. *)
  type hook = Configuration.t -> Label.t -> State.t -> unit

  (** Add a transition to the automaton. *)
  val add_transition : ?hook:hook -> Configuration.t -> Label.t -> State.t -> t -> t

  (** Add a transition to the automaton, and nothing else.
      Note that it is an internal method that should not be called by users. *)
  val add_transition_unchecked : Configuration.t -> Label.t -> State.t -> t -> t
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

  (* module TypedConfiguration : TypedPattern.S with module Term = Term and module Type = Type and module Var = State and module TypedTerm = TypedTerm and module Pattern = Configuration *)
  (* module TypedConfiguration : module type of TypedPattern.Make (TypedTerm) (VarPattern) *)
  module BoundConfiguration : TypedPattern.S with type Sym.t = Sym.t and type Var.t = Var.t and type Type.t = Binding.t

  type transition = Configuration.t * Label.t * State.t

  (* val all: Label.t -> State.t -> Sym.t list -> t *)
  (** [all alphabet] the automaton recognizing all the terms build from alphabet. *)

  val alphabet: t -> SymSet.t
  (** Get the alphabet on which the automaton is defined. *)

  (** Computes the set of all states composing the automaton.
      Note this can be time consuming for large automata.
  *)
  val states : t -> StateSet.t

  val is_final : t -> State.t -> bool
  (** [is_final aut q] Check if a given state is a final state. *)

  (** Computes the of states in the automaton.
      Note this can be time consuming for large automata.
  *)
  val state_count : t -> int

  val is_state_empty : State.t -> t -> bool
  (** [is_state_empty q t] Checks if the given state [q] is empty (recognises no term) in [t]. *)

  val configurations_for_state : State.t -> t -> LabeledConfigurationSet.t
  (** Returns the set of configuration generating a given state. Complexity O(log(n)). *)

  val states_for_configuration : Configuration.t -> t -> LabeledStateSet.t
  (** Find a state recognizing this configuration. Complexity O(log(n)). *)

  val sub_states_of : t -> State.t -> StateSet.t
  (* [sub_states_of aut q] return the set of states [q'] such that [aut]
     contains the transition [q'] -> [q]. *)

  val fold_configurations_for_binding : (LabeledConfiguration.t -> State.t -> 'a -> 'a) -> Binding.t -> t -> 'a -> 'a
  val iter_configurations_for_binding : (LabeledConfiguration.t -> State.t -> unit) -> Binding.t -> t -> unit

  val fold_configurations_for_epsilon_state : (Configuration.t -> 'a -> 'a) -> State.t -> t -> 'a -> 'a
  val iter_configurations_for_epsilon_state : (Configuration.t -> unit) -> State.t -> t -> unit

  val fold_epsilon_class : (State.t -> 'a -> 'a) -> State.t -> t -> 'a -> 'a

  (** Find all non-epsilon configurations using this state, skipping epsilon transitions.
      The resulting transition may not *directly* use the state. *)
  val state_transitive_parents : State.t -> t -> ConfigurationSet.t

  (** Build the automaton for which each transition is reachable from one of the given state.
      The given input states becomes the final states. *)
  val sub_automaton : StateSet.t -> t -> t

  val mem : Configuration.t -> Label.t -> State.t -> t -> bool

  (** Check if this configuration is connected to a state in this automaton. *)
  val mem_configuration : Configuration.t -> t -> bool

  (** Check if this state is connected to a configuration in this automaton,
      or if it is a final state. *)
  val mem_state : State.t -> t -> bool

  val type_term_in : State.t -> Sym.t Term.term -> t -> BoundTerm.t option

  val type_term : Sym.t Term.term -> t -> BoundTerm.t option

  val recognizes_in : State.t -> Sym.t Term.term -> t -> bool

  val recognizes : Sym.t Term.term -> t -> bool

  val recognizes_state_in : State.t -> State.t -> t -> bool
  (** [recognizes_state_in a b t] checks if state [a] recognizes state [b] in [t]. *)

  val pick_binding_inhabitant : ?epsilon:bool -> Binding.t -> t -> BoundTerm.t

  val pick_binding_inhabitant_opt : ?epsilon:bool -> Binding.t -> t -> BoundTerm.t option

  val pick_term : ?smallest:bool -> ?epsilon:bool -> t -> BoundTerm.t

  val pick_term_opt : ?smallest:bool -> ?epsilon:bool -> t -> BoundTerm.t option

  val pick_term_in : ?epsilon:bool -> State.t -> t -> BoundTerm.t

  val pick_term_in_opt : ?epsilon:bool -> State.t -> t -> BoundTerm.t option

  val pick_term_in_intersection : ?epsilon:bool -> StateSet.t -> t -> Sym.t Term.term

  val pick_term_in_intersection_opt : ?epsilon:bool -> StateSet.t -> t -> Sym.t Term.term option

  val map : ?filter:(Configuration.t -> Label.t -> State.t -> t -> bool) -> (Label.t -> Label.t) -> (State.t -> State.t) -> t -> t
  (** Map each state/label of the automaton. *)

  val filter : (Configuration.t -> Label.t -> State.t -> bool) -> t -> t
  (** keep only the transition satisfying a given predicate. *)

  val fold_states : (State.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold states *)

  val fold_transitions : (Configuration.t -> Label.t -> State.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold transitions *)

  val fold_transition_pairs : ?reflexive:bool -> (Configuration.t -> Label.t -> State.t -> Configuration.t -> Label.t -> State.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold pair of transitions. If [reflexive] is true, include pairs of the same transition. By default [reflexive] is false. *)

  val label : ((State.t -> 'a) -> State.t -> 'a) -> (State.t -> 'a) -> t -> (State.t -> 'a)
  (** Label computation utility.
      label f g t
      f takes a function 'bottom', a state q and returns a value.
      'bottom' gives the already computed value of a state 'below' q in the tree/graph.
      If q is in a cycle, then (g q) is called to give a default value to q.
      Returns a label function associating a value to each state. *)

  val merge : t -> t -> t
  (** Merge the transitions of two automata.
      If the set of states is disjoined between the two automata,
      return the union of the the two automata. *)

  val inter : ?hook:(t -> State.t -> unit) -> (data -> data -> data) -> t -> t -> t
  (** Computes the intersection of two automata.
      Preserves determinism.
      The resulting automaton is not reduced.
      hook is called for each state of the produced automaton, with a partially built automaton. *)

  val reachable_states : ?epsilon:bool -> t -> StateSet.t
  (* Return the set of reachable states. *)

  val reduce : ?epsilon:bool -> ?from_finals:bool -> t -> t
  (** Remove non reachable states and transitions.
      Set [epsilon] to false to ignore epsilon transition.
      Set [from_finals] to false (default true) to treat each state as final. *)

  val complete : ?with_states:StateSet.t -> (Configuration.t -> State.t * Label.t) -> Sym.t list -> t -> t
  (** [complete lbl r F t] Complete the automaton such that for all symbol f of [F]
      and states q_1 ... q_n (ar(f) = n), there exists a state q such that
      f(q_1, ..., q_n) -> q. If the function can't find such state q, it will use the state r
      and add the transition f(q_1, ..., q_n) -> r.
      Complexity: O(|F|x|Q|^ar(F)). *)

  val complement : t -> t
  (** [complement t] Computes the complement of a complete DFTA.
      Complexity: linear in the number of states.
      If you don't know if your automaton is complete or deterministic,
      you have to call [Automaton.determinise] and [Automaton.complete],
      which could cause an exponential blow-up. *)

  val unepsilon : t -> t
  (** Removes all epsilon-transition from an automaton. TODO *)

  val determinise : ?init_classes:StateSet.t -> (StateSet.t -> State.t) -> t -> t
  (** Computes the DFTA version of a NFTA.
      This algorithm create a new automaton by grouping in the same equivalence class (set of states)
      states with non-empty intersection languages.
      The first parameter is used to create a state for a given class/intersection of states.*)

  val determinise_typed : ?init_classes:StateSet.t -> (module TYPE with type t = 'a) -> (State.t -> 'a) -> (StateSet.t -> 'a -> State.t) -> t -> t
  (** Computes the DFTA version of a NFTA.
      This algorithm create a new automaton by grouping in the same equivalence class (set of states)
      states with non-empty intersection languages.
      The first parameter is used to create a state for a given class/intersection of states.
      States are typed with [Type.t] using the [type_of] function. States with different types will be
      placed in different equivalence classes.  *)

  val minimalise : ?filter:(State.t -> State.t -> bool) -> t -> t
  (** Computes the minimal version of a DFTA.
      Two states qa qb are equivalent (and thus merged) if:
      - for each f(q0, ..., qk, qa, qk+2, ..., qn) -> q there exists
                 f(q0, ..., qk, qb, qk+2, ..., qn) -> q and
      - if qa is final <=> qb is final and
      - if filter is given, (filter qa qb) = true. *)

  type renaming = State.t StateMap.t
  (* Represents the current knowledge of the renaming checker functions.
     If such function returns [Some true], then the input states are considered
     roots of syntaxically equivalent trees. If it returns [Some false],
     then they are considered syntaxically differents. If it returns [None],
     we don't know, and the algorithm will have to check by itself.
     You can use this function to start the renaming algorithm with some knowledge.
     For instance giving [Some true] when [State.equal] returns true, and else [None]. *)

  val state_renaming : ?knowledge:renaming -> t -> t -> State.t -> State.t -> State.t StateMap.t option
  (* [state_renaming knowledge a b] Find a renaming from [b] to [a] such that
     [qa] and [qb] are equivalents.
     Note that this function does not return a complete renaming:
     only the states needed for the syntaxic equivalence are considered.
     See [renaming_knowledge] to know how [knowledge] is used.

     NOTE this function assumes that the trees recognized by [qa] and [qb] are deterministic and normalized. *)

  type normalizer = Sym.t -> State.t list -> LabeledState.t

  (** Add a transition to the automaton.
      If [normalize] is set, the configuration is normalized but not the final transition. *)
  val add_normalized_transition : ?hook:hook -> normalizer -> Configuration.t -> Label.t -> State.t -> t -> t

  (** Add multiple transitions to the automaton.
      If [normalize] is set, the configurations are normalized but not the finals transitions. *)
  val add_normalized_transitions : ?hook:hook -> normalizer -> transition list -> t -> t

  (** Add multiple configurations to the automaton.
      If [normalize] is set, the configurations are normalized but not the finals transitions. *)
  val add_configurations_to : ?normalizer:normalizer -> ?hook:hook -> LabeledConfiguration.t list -> State.t -> t -> t

  val add_configuration : normalizer -> ?hook:hook -> Configuration.t -> t -> BoundConfiguration.t * t

  (** Returns (q, [a]) recognizing the configuration [t]. *)
  val add : normalizer -> ?hook:hook -> Configuration.t -> t -> BoundConfiguration.t * t

  (** Create a normalized automaton recognizing a given term. *)
  val of_term : normalizer -> Sym.t Term.term -> data -> t

  (** Create a normalized automaton recognizing a given list of terms. *)
  val of_terms : normalizer -> (Sym.t Term.term) list -> data -> t

  val compare : t -> t -> int

  (** Pretty-print the autmaton. *)
  val print : t -> Format.formatter -> unit

  (** Operations with patterns. *)
  module Patterns (X : Pattern.VARIABLE) : sig
    type pattern = (Sym.t, X.t) Pattern.pattern

    val recognizes_pattern : pattern -> t -> bool
    val recognizes_pattern_in : State.t -> pattern -> t -> bool
    val configuration_of_pattern : (X.t -> State.t) -> pattern -> Configuration.t
  end

  type dynamic_filter =
    | NoFilter
    | Filter of (State.t -> Label.t -> (bool * dynamic_filter))

  (** Operations with typed patterns. *)
  module BoundPatterns (X : Pattern.VARIABLE) : sig
    type bound_pattern = (Sym.t, X.t, Binding.t) TypedPattern.typed_pattern

    val fold_pattern_instances : ?epsilon_f:((bound_pattern -> bool) option) -> ?filter:dynamic_filter -> (BoundTerm.t -> 'a -> 'a) -> bound_pattern -> t -> 'a -> 'a
    (** [fold_pattern_instances f pattern aut x] Fold all the possible cycle-free pattern instances.
        Since we forbid cycles, this function always terminates. *)

    (* val type_pattern_opt : BoundPattern.t -> t -> BoundPattern.t option *)
    (* [type_pattern_opt pattern aut] try to give proper type to a given [pattern].
       If the pattern is not recognized by [aut], then returns None. *)

    val instanciate_pattern_opt : ?epsilon:bool -> bound_pattern -> t -> BoundTerm.t option
    (* [instanciate_pattern_opt gen pattern aut] instanciate the variables in [pattern]
       into terms recognized by [aut]. Note that [pattern] may not be recognized by [aut].
       Use [type_pattern_opt] before (or after) to make sure that the pattern is recognized by [aut].
       Variables must be typed (non None type). *)

    val recognizes_bound_pattern : ?epsilon:bool -> bound_pattern -> t -> bool
    val recognizes_bound_pattern_in : ?debug:bool -> ?epsilon:bool -> State.t -> bound_pattern -> t -> bool
  end
end

module Extend (B: BASE) : sig
  include S with module Sym = B.Sym
             and module State = B.State
             and module Label = B.Label
             and module Configuration = B.Configuration
             and module LabeledConfiguration = B.LabeledConfiguration
             and module LabeledState = B.LabeledState
             and module StateSet = B.StateSet
             and module StateMap = B.StateMap
             and module ConfigurationSet = B.ConfigurationSet
             and module ConfigurationMap = B.ConfigurationMap
             and module LabeledConfigurationSet = B.LabeledConfigurationSet
             and type t = B.t
             and type data = B.data
             and type hook = B.hook
end

(** Tree Automaton. *)
module Make (F : Symbol.S) (Q : STATE) (L : LABEL) : sig
  include S with module Sym = F and module State = Q and module Label = L and type data = unit

  val empty : t
end

(** External operations. *)
module Ext (A : S) (B : S with module Sym = A.Sym) : sig
  val map : ?filter:(A.Configuration.t -> A.Label.t -> A.State.t -> bool) -> (A.data -> B.data) -> (A.Label.t -> B.Label.t) -> (A.State.t -> B.State.t) -> A.t -> B.t

  val states_intersection_opt : A.State.t -> B.State.t -> A.t -> B.t -> (A.BoundTerm.t * B.BoundTerm.t) option

  val states_intersects : A.State.t -> B.State.t -> A.t -> B.t -> bool
  (** Tests if the languages of two states intersects.
      Note: we suppose here that the two automata are normalized. *)

  val state_included_in : ?epsilon:bool -> A.t -> B.t -> A.State.t -> B.State.t -> B.BoundTerm.t option
  (** Test if  L([b]) is included in L([a]).
      We suppose that both state languages are epsilon free and normalized.
      Return None if the language is included, or a sample term that is not included.
      If [epsilon] is set to true (which is by default), epsilon transition are allowed,
      but in [b] only. *)

  type renaming = A.State.t B.StateMap.t
  (* Represents the current knowledge of the renaming checker functions.
     If such function returns [Some true], then the input states are considered
     roots of syntaxically equivalent trees. If it returns [Some false],
     then they are considered syntaxically differents. If it returns [None],
     we don't know, and the algorithm will have to check by itself.
     You can use this function to start the renaming algorithm with some knowledge.
     For instance giving [Some true] when [State.equal] returns true, and else [None]. *)

  val state_renaming : ?epsilon:bool -> ?knowledge:renaming -> (A.Label.t -> B.Label.t -> bool) -> A.t -> B.t -> A.State.t -> B.State.t -> renaming option
  (* [state_renaming ?epsilon ?knowledge a b] Find a renaming from [b] to [a] such that
     [qa] and [qb] are equivalents.
     Note that this function does not return a complete renaming:
     only the states needed for the syntaxic equivalence are considered.
     See [renaming_knowledge] to know how [knowledge] is used.

     NOTE this function assumes that the trees recognized by [qa] and [qb] are deterministic and normalized. *)
end

module Product (A : S) (B : S with module Sym = A.Sym) (AB : S with module Sym = B.Sym) : sig
  (** External intersection. *)
  val product : ?hook:(AB.t -> AB.State.t -> unit) -> ?epsilon:bool -> (A.data -> B.data -> AB.data) -> (A.Label.t -> B.Label.t -> AB.Label.t option) -> (A.State.t -> B.State.t -> AB.State.t option) -> A.t -> B.t -> AB.t
end

module MakeStateOption (Q : STATE) : STATE with type t = Q.t option
module MakeStateProduct (A : STATE) (B : STATE) : STATE with type t = A.t * B.t
