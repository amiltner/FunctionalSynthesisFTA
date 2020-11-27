open Tool

module FTAS = FTASynthesizer.Create(TimbukVataBuilder.Make)
(* module FTAS = FTASynthesizer.Create(Automata.VATABuilder) *)

let mk_aut
  ()
  : unit =
  print_endline "hi";
  let autid = "A" in
  let myaut = TimbukSpec.Spec.Aut.create () in
  let myaut =
    TimbukSpec.Spec.Aut.add_transition
      (TimbukSpec.Spec.Aut.Configuration.Cons (Sym (Timbuk.StringSymbol.create "a" 0),[]))
      ()
      (PolyBase (TimbukSpec.UserState.of_string "c"))
      myaut
  in
  let a =
    TimbukSpec.Spec.Automata.add
      autid
      (Codemap.Span.located Codemap.Span.default myaut)
      TimbukSpec.Spec.Automata.empty
  in
  MyStdLib.SimpleFile.write_to_file ~fname:"a.out" ~contents:(MyStdLib.to_string_of_printer TimbukSpec.Spec.Automata.print a)

type error =
  | Parse of TimbukSpec.Parse.error * Codemap.Span.t

exception Error of error

let error_content = function
  | Parse (_, span) -> (None, Some span)


let format_error_hints fmt = function
  | Parse _ -> ()
let error_kind = function
  | Parse _ -> "syntax error"


let error_message = function
  | Parse _ -> None


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
      let fmt = Codemap.Formatter.create () in
      let viewport = Codemap.Span.from_start (Codemap.Span.aligned ~margin:1 span) in
      Codemap.Formatter.add fmt span label_opt Codemap.Formatter.Highlight.Error;
      format_error_hints fmt e;
      Codemap.Formatter.print fmt input viewport stderr
    | None -> ()
  end


let rd_aut
    ()
  : unit =
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
  in
  let f = open_in "../holder" in
  let inp = seq_of_channel f in
  let utf8_input = Unicode.Encoding.utf8_decode inp in
  begin try
      begin try
          print_endline "before";
  let lexer = TimbukSpec.Lexer.create utf8_input in
  let ast = TimbukSpec.Parse.specification lexer in
  print_endline "after";
  let spec = TimbukSpec.Build.specification ast in
  print_endline (MyStdLib.print_to_string TimbukSpec.Spec.print spec)
    with
    | TimbukSpec.Parse.Error (e, span) -> raise (Error (Parse (e, span)))
  end
    with
    | Error e ->
      format_error utf8_input e Format.err_formatter;
      exit 1
  end


let synthesize_solution
    (fname:string)
    (use_myth:bool)
    (use_l2:bool)
    (log:bool)
  : unit =
  (*rd_aut ();*)
  Consts.logging := log;
  let p_unprocessed =
    Parser.unprocessed_problem
      Lexer.token
      (Lexing.from_string
         (Prelude.prelude_string ^ (MyStdLib.SimpleFile.read_from_file ~fname)))
  in
  let problem = Problem.process p_unprocessed in
  let e =
    if use_myth then
      MythSynthesisCaller.myth_synthesize
        ~problem
    else if use_l2 then
      MythSynthesisCaller.myth_synthesize_print ~problem
        (* then we can call l2 *)
    else
      FTAS.synth ~problem
  in
  print_endline (Expr.show e)

open MyStdLib.Command.Let_syntax
let param =
  MyStdLib.Command.basic ~summary:"..."
    [%map_open
      let input_spec  = anon ("input_spec" %: string)
      and use_myth   = flag "use-myth" no_arg ~doc:"Solve using the myth synthesis engine"
      and log   = flag "log" no_arg ~doc:"log process"
      and use_l2   = flag "use-l2" no_arg ~doc:"Solve using the l2 synthesis engine"
      (*and no_grammar_output   = flag "no-grammar-output" no_arg ~doc:"do not output the discovered grammar"
      and log_progress   = flag "log-progress" no_arg ~doc:"output the progress log"
      and print_runtime_specs  = flag "print-runtime-specs" no_arg ~doc:"output the runtime specs"
      and run_experiments  = flag "run-experiments" no_arg ~doc:"output experient info"
      and positive_examples  = flag "pos" (listed string) ~doc:"path positive example path"
      and negative_examples  = flag "neg" (listed string) ~doc:"path negative example path"
      and pos_ndfo  = flag "pos-ndf" (optional string) ~doc:"path newline delimited positive example path"
        and neg_ndfo  = flag "neg-ndf" (optional string) ~doc:"path newline delimited negative example path"*)
      in
      fun () ->
        synthesize_solution
          input_spec
          use_myth
          use_l2
          log
    ]

let () =
  Core.Command.run
    param
