open Collections
open Timbuk
open TimbukTyping
open CodeMap

module Symbol = AppSymbol.Make (StringSymbol)
module Base = UserState

module MonoType = struct
  include GenericTypes.Mono (Base)

  let construct = function
    | MonoType.Base ty -> ty
    | MonoType.Fun (a, b) -> GenericTypes.Fun (a, b)

  let destruct = function
    | GenericTypes.Base ty -> MonoType.Base (GenericTypes.Base ty)
    | GenericTypes.Fun (a, b) -> MonoType.Fun (a, b)
end

module PolyType = struct
  include GenericTypes.Poly (Base)

  type mono = MonoType.t

  type var = int

  let destruct = function
    | GenericTypes.PolyVar _ -> raise (Invalid_argument "cannot destruct internal type variable")
    | GenericTypes.Polymorphic x -> PolyType.Poly x
    | GenericTypes.PolyBase ty -> PolyType.Base (GenericTypes.PolyBase ty)
    | GenericTypes.PolyFun (a, b) -> PolyType.Fun (a, b)

  let rec monomorphic = function
    | GenericTypes.PolyBase ty -> GenericTypes.Base ty
    | GenericTypes.PolyFun (a, b) -> GenericTypes.Fun (monomorphic a, monomorphic b)
    | _ -> raise (Invalid_argument "type is not monomorphic")
end

module State = PolyType

module Term = Term.Make (Symbol)
module Label = NoLabel

module LocType = struct
  type t = State.t option * Span.t

  let product (q1, s1) (q2, s2) =
    match q1, q2 with
    | Some q1, Some q2 ->
      if State.compare q1 q2 = 0 then
        Some (Some q1, s1)
      else
        None
    | Some q1, _ -> Some (Some q1, s1)
    | _, Some q2 -> Some (Some q2, s2)
    | _, _ -> Some (None, s1)

  let compare (q1, _) (q2, _) =
    match q1, q2 with
    | Some q1, Some q2 -> State.compare q1 q2
    | Some _, None -> 1
    | None, Some _ -> -1
    | None, None -> 0

  let equal (q1, _) (q2, _) =
    match q1, q2 with
    | Some q1, Some q2 -> State.equal q1 q2
    | None, None -> true
    | _, _ -> false

  let hash (q, _) = Hashtbl.hash q

  let print (t, _) out =
    match t with
    | Some q ->
      (*				Format.pp_print_string ppf ":";*)
      State.print q out
    | None ->
      Format.fprintf out "~"
end

module Pattern = Pattern.Make (Symbol) (Var)
module Aut = Automaton.Make (Symbol) (State) (Label)

module LocPattern = TypedPattern.Make (Symbol) (Var) (LocType)
module TargetTypeLocPattern = struct
  type t = LocPattern.t * Aut.StateSet.t option

  let compare (pa, ta) (pb, tb) =
    let c = LocPattern.compare pa pb in
    if c = 0 then begin
      match ta, tb with
      | Some ta, Some tb -> Aut.StateSet.compare ta tb
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0
    end else c

  let equal a b =
    compare a b = 0

  let print (pattern, target_ty) fmt =
    match target_ty with
    | Some ty -> Format.fprintf fmt "%t :: {%t}" (LocPattern.print pattern) (Aut.StateSet.print Aut.State.print ", " ty)
    | None -> LocPattern.print pattern fmt
end
module LocPatternSet = Set.Make (TargetTypeLocPattern)
module LocRule = Rule.Make (LocPattern)
module LocTrs = Relation.Make (LocPattern) (LocRule)

module Rule = Rule.Make (Pattern)
module Trs = Relation.Make (Pattern) (Rule)

module PatternSet = struct
  type t = LocPatternSet.t * Aut.t option
end

let print_id id out =
  Format.fprintf out "%s" id

module Id = struct
  type t = string

  let compare = String.compare
end

module Alphabet = Alphabet.Make (Id) (Symbol)

module Variables = struct
  include Dictionary.Make (Id) (Var)

  let print t out =
    let print_var id _ =
      Format.fprintf out "%t " (print_id id)
    in
    iter print_var t
end

module Trss = struct
  include Dictionary.Make (Id) (LocTrs)

  let print t out =
    let print_trs id (trs, _) =
      Format.fprintf out "TRS %t\n%t" (print_id id) (LocTrs.print trs)
    in
    iter print_trs t
end

module Automata = struct
  include Dictionary.Make (Id) (Aut)

  let print t out =
    let print_automaton id (aut, _) =
      Format.fprintf out "Automaton %t\n%t" (print_id id) (Aut.print aut)
    in
    iter print_automaton t
end

module PatternSets = struct
  include Dictionary.Make (Id) (PatternSet)

  let print t out =
    let print_pattern p =
      Format.fprintf out "%t\n" (TargetTypeLocPattern.print p)
    in
    let print_pattern_set id ((set, _), _) =
      Format.fprintf out "Patterns %t\n" (print_id id);
      LocPatternSet.iter print_pattern set
    in
    iter print_pattern_set t
end

type t = {
  spec_alphabet : Alphabet.t;
  spec_variables : Variables.t;
  spec_trss : Trss.t;
  spec_automata : Automata.t;
  spec_pattern_sets : PatternSets.t
}

(* let state_table = Hashtbl.create 8 *)

(* let state_of_string id =
   match Hashtbl.find_opt state_table id with
   | Some q -> q
   | None ->
    let q = State.create () in
    Hashtbl.add state_table id q;
    Format.eprintf "state %s -> %t@." id (State.print q);
    q *)

let state_of_string id =
  GenericTypes.PolyBase (UserState.of_string id)

let print spec out =
  Format.fprintf out "Ops\n%t\nVars\n%t\n%t%t%t\n"
    (Alphabet.print spec.spec_alphabet)
    (Variables.print spec.spec_variables)
    (Trss.print spec.spec_trss)
    (Automata.print spec.spec_automata)
    (PatternSets.print spec.spec_pattern_sets)
