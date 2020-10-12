open CodeMap

type item_kind =
  | Atom (* symbol, variable or state *)
  | Trs
  | Automaton
  | PatternSet

type error =
  | ProtectedSymbol of string
  | AlreadyDefined of string * item_kind * Span.t
  | UndefinedSymbolOrVar of string
  | UndefinedSymbolOrState of string
  | UndefinedState of string
  | UndefinedAutomaton of string
  | VariableSubterms of string * Span.t (* give the variable definition site. *)
  | StateSubterms of string * Span.t (* give the variable definition site. *)
  | InvalidArity of int * int * Span.t (* give the found arity, the expected arity, and the symbol def site. *)
  | NotAState of Span.t (* when a configuration has a non-state rhs. *)
  | NoTypeSystem of string * Span.t

exception Error of error * Span.t

val specification : Ast.specification Span.located -> Spec.t
(** Build a Timbuk specification from a specification ast. *)

val print_error : error -> Format.formatter -> unit

val error_label : error -> string option

val format_error_hints : error -> Formatter.t -> unit
