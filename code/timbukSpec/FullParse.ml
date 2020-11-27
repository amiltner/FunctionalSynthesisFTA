open Collections
open Codemap
open Timbuk
open TimbukSolving
open Spec
open Unicode
open UString

module Integer = struct
  type t = int

  let compare a b = a - b

  let print i fmt =
    Format.fprintf fmt "%d" i
end

module Cvc4Conf = struct
  let path () = "cvc4"

  let count = ref 0

  let log () =
    (* let i = !count in
       count := i + 1;
       let filename = "log/cvc4_" ^ (string_of_int i) ^ ".smt2" in
       Some (filename, open_out filename) *)
    None
end

(* Polymorphic typing. *)
module LocPolyType = struct
  type t = PolyType.t * Codemap.Span.t
  let compare (a, _) (b, _) = PolyType.compare a b
  let equal (a, _) (b, _) = PolyType.equal a b
  let product (a, span) (b, _) =
    match PolyType.product a b with
    | Some t -> Some (t, span)
    | None -> None
  let hash (t, _) = PolyType.hash t
  let print (t, _) fmt = PolyType.print t fmt
end
module PolyTypedPattern = TypedPattern.Make (Aut.Sym) (Pattern.Var) (LocPolyType)
module PolyTypedRule = Timbuk.Rule.Make (PolyTypedPattern)
module PolyTypedTrs = Relation.Make (PolyTypedPattern) (PolyTypedRule)
module PolyTyper = TimbukTyping.Poly.Make (Codemap.Span) (Symbol) (Base) (Aut) (LocPattern) (LocTrs) (PolyTypedTrs)

(* Monomorphic typing. *)
module MonoSym = struct
  type t = Aut.Sym.t * MonoType.t list * MonoType.t
  let compare (fa, la, ta) (fb, lb, tb) =
    let c = Aut.Sym.compare fa fb in
    if c = 0 then
      let c = MonoType.compare ta tb in
      if c = 0 then List.compare MonoType.compare la lb else c
    else c
  let equal (fa, la, ta) (fb, lb, tb) = Aut.Sym.equal fa fb && MonoType.equal ta tb && List.equal MonoType.equal la lb
  let arity (f, _, _) = Aut.Sym.arity f
  let hash = Hashtbl.hash
  let print (f, _, _) fmt = Aut.Sym.print f fmt
  (* let print (f, l, ty) fmt =
     Format.fprintf fmt "[%t:%t:%t]" (Aut.Sym.print f) (List.print MonoType.print "," l) (MonoType.print ty) *)
end
module MonoTerm = Timbuk.Term.Make (MonoSym)
module LocMonoType = struct
  type t = MonoType.t * Codemap.Span.t
  let compare (a, _) (b, _) = MonoType.compare a b
  let equal (a, _) (b, _) = MonoType.equal a b
  let product (a, span) (b, _) =
    match MonoType.product a b with
    | Some t -> Some (t, span)
    | None -> None
  let hash (t, _) = MonoType.hash t
  let print (t, _) fmt = MonoType.print t fmt
end
module MonoAut = Automaton.Make (MonoSym) (MonoType) (Aut.Label)
module MonoTypedPattern = TypedPattern.Make (MonoSym) (Pattern.Var) (LocMonoType)
module MonoTypedRule = Timbuk.Rule.Make (MonoTypedPattern)
module MonoTypedTrs = Relation.Make (MonoTypedPattern) (MonoTypedRule)
module MonoTyper = TimbukTyping.Mono.Make (Codemap.Span) (Symbol) (MonoType) (PolyType) (Aut) (PolyTypedPattern) (PolyTypedTrs) (MonoAut) (MonoTypedPattern) (MonoTypedTrs)

(* Subtype typer. *)
module SubTyper = TimbukTyping.Sub.Make (Codemap.Span) (MonoAut) (MonoTypedPattern) (MonoTypedTrs)

(* Regular typing. *)
module Solver = Cvc4.Make (Cvc4Conf) (MonoAut.State)
module AbsSolver = Cvc4.Make (Cvc4Conf) (Integer)
module TypeSystem = TimbukTyping.RefinedTypeSystem.Make (MonoAut)
module RegularTyper = TimbukTyping.Regular.Make (Codemap.Span) (TypeSystem) (MonoTypedPattern) (MonoTypedTrs) (Solver) (AbsSolver)
module RegularType = RegularTyper.RegularType

let rec instanciate_pattern aut = function
  | RegularTyper.RegularTypedPattern.Cons (f, l), _ ->
    MonoTerm.Term (f, List.map (instanciate_pattern aut) l)
  | RegularTyper.RegularTypedPattern.Var x, (ty, _) ->
    let ty = MonoAut.StateSet.choose ty in
    MonoAut.BoundTerm.strip (MonoAut.pick_term_in ty aut)
  | RegularTyper.RegularTypedPattern.Cast pattern, _ ->
    instanciate_pattern aut pattern

type runtime_error =
  | IrreducibleNonValue of MonoTerm.t
  | InvalidTargetType of MonoAut.StateSet.t * RegularTyper.RegularTypePartition.t
  | RegularTypeMissmatch of RegularTyper.RegularType.t * RegularTyper.RegularTypedPattern.t * MonoAut.t

type error =
  | Parse of Parse.error * Codemap.Span.t
  | Build of Build.error * Codemap.Span.t
  | PolyType of PolyTyper.error * Codemap.Span.t
  | MonoType of MonoTyper.error * Codemap.Span.t
  | SubType of SubTyper.error * Codemap.Span.t
  | RegularType of RegularTyper.error
  | Runtime of runtime_error

exception Error of error

let error_kind = function
  | Parse _ -> "syntax error"
  | Build (e, _) -> "build error"
  | PolyType (e, _) -> "polymorphic type error"
  | MonoType (e, _) -> "monomorphic type error"
  | SubType (e, _) -> "sub-type error"
  | RegularType _ -> "regular type error"
  | Runtime e -> "runtime error"

let error_message = function
  | Parse _ -> None
  | Build (e, _) -> Some (Format.asprintf "%t" (Build.print_error e))
  | PolyType (e, _) -> Some (Format.asprintf "%t" (PolyTyper.print_error e))
  | MonoType (e, _) -> Some (Format.asprintf "%t" (MonoTyper.print_error e))
  | SubType (e, _) -> Some (Format.asprintf "%t" (SubTyper.print_error e))
  | RegularType (RegularTyper.BiTypedTerm (_, q, q', _)) ->
    Some (Format.asprintf "unable to separate types `%t' and `%t'" (RegularTyper.TypeAut.State.print q) (RegularTyper.TypeAut.State.print q'))
  | Runtime (IrreducibleNonValue term) ->
    Some (Format.asprintf "the following term is irreduce but is not a value:\n%t" (MonoTerm.print term))
  | Runtime (InvalidTargetType (target_ty, partition)) ->
    let print_partition_elt elt fmt =
      Format.fprintf fmt "{%t}" (MonoAut.StateSet.print MonoType.print ", " elt)
    in
    Some (Format.asprintf "the given target type `%t` is not in the type partition `{%t}'"
            (RegularType.print target_ty)
            (RegularTyper.RegularTypePartition.print print_partition_elt ", " partition))
  | Runtime (RegularTypeMissmatch (expected_ty, (_, (found_ty, _)), _)) ->
    Some (Format.asprintf "expected regular type `%t', found `%t'" (RegularType.print expected_ty) (RegularType.print found_ty))

let error_content = function
  | Parse (_, span) -> (None, Some span)
  | Build (e, span) -> (Build.error_label e, Some span)
  | PolyType (e, span) -> (PolyTyper.error_label e, Some span)
  | MonoType (e, span) -> (MonoTyper.error_label e, Some span)
  | SubType (e, span) -> (SubTyper.error_label e, Some span)
  | RegularType _ -> (None, None)
  | Runtime _ -> (None, None)

let format_error_hints fmt = function
  | Parse _ -> ()
  | Build (e, _) -> Build.format_error_hints e fmt
  | PolyType (e, _) ->
    begin
      match e with
      | TypeMissmatch (expected_ty, Some expected_span, _) ->
        let msg = Format.asprintf "type `%t' is required here" (Aut.State.print expected_ty) in
        Codemap.Formatter.add fmt expected_span (Some msg) Codemap.Formatter.Highlight.Note
      | _ -> ()
    end
  | MonoType (_e, _) -> ()
  | SubType (_e, _) -> ()
  | RegularType _ -> ()
  | Runtime _ -> ()

let help ppf f =
  Format.fprintf ppf "\x1b[1;34mnote: \x1b[0m";
  f (Format.fprintf ppf);
  Format.fprintf ppf "@."

let print_error_help ppf = function
  | Runtime (RegularTypeMissmatch (expected_ty, found_pattern, aut)) ->
    let sample = instanciate_pattern aut found_pattern in
    help ppf (fun m -> m "here is a term that may not rewrite to %t:\n\n      \x1b[1;1m%t\x1b[0m\n" (RegularType.print expected_ty) (MonoTerm.print sample));
  | _ -> ()

let format_error input e ppf =
  let label_opt, span_opt = error_content e in
  let msg_opt = error_message e in
  Format.fprintf ppf "\x1b[1;31m%s\x1b[0m\x1b[1;1m" (error_kind e);
  begin match span_opt with
    | Some span -> Format.fprintf ppf " (%t)" (Codemap.Span.format span)
    | None -> ()
  end;
  begin match msg_opt with
    | Some msg -> Format.fprintf ppf ": %s" msg
    | None -> ()
  end;
  Format.fprintf ppf "\x1b[0m@.";
  begin match span_opt with
    | Some span ->
      let fmt = Formatter.create () in
      let viewport = Span.from_start (Span.aligned ~margin:1 span) in
      Formatter.add fmt span label_opt Formatter.Highlight.Error;
      format_error_hints fmt e;
      Formatter.print fmt input viewport stderr
    | None -> ()
  end;
  print_error_help ppf e

(** Make a sequence of char out of an input channel. *)
let seq_of_channel input =
  let rec next mem () =
    match !mem with
    | Some res -> res
    | None ->
      let res =
        try
          let c = input_char input in
          Seq.Cons (c, next (ref None))
        with
        | End_of_file -> Seq.Nil
      in
      mem := Some res;
      res
  in
  next (ref None)


let process_file filename =
  (* let open Log in *)
  let file = open_in filename in
  let input = seq_of_channel file in
  let utf8_input = Unicode.Encoding.utf8_decode input in
  begin try
      begin try
          let lexer = Lexer.create utf8_input in
          let ast = Parse.specification lexer in
          ast
        with
        | Parse.Error (e, span) -> raise (Error (Parse (e, span)))
        | Build.Error (e, span) -> raise (Error (Build (e, span)))
        | PolyTyper.Error (e, span) -> raise (Error (PolyType (e, span)))
        | MonoTyper.Error (e, span) -> raise (Error (MonoType (e, span)))
        | SubTyper.Error (e, span) -> raise (Error (SubType (e, span)))
        | RegularTyper.Error e -> raise (Error (RegularType e))
        (* | Runtime.Error e -> raise (Error (Runtime (e, span))) *)
      end
    with
    | Error e ->
      format_error utf8_input e Format.err_formatter;
      exit 1
  end

let full_parse_to_ast
    (s:string)
  : Ast.automaton Codemap.Span.located =
  List.hd (fst (process_file s)).spec_automata
