open Tool


let synthesize_solution
    (fname:string)
    (use_myth:bool)
    (use_l2:bool)
    (log:bool)
    (print_times:bool)
    (tc_synth:bool)
    (use_timbuk:bool)
    (print_mapping:bool)
  : unit =
  (*rd_aut ();*)
  Consts.logging := log;
  Consts.print_mapping := print_mapping;
  let p_unprocessed =
    Parser.unprocessed_problem
      Lexer.token
      (Lexing.from_string
         (Prelude.prelude_string ^ (MyStdLib.SimpleFile.read_from_file ~fname)))
  in
  let problem = Problem.process p_unprocessed in
  let synth =
    if use_myth then
      (module MythSynthesisCaller : Synthesizer.S)
    else if use_l2 then
      (module L2SynthesisCaller : Synthesizer.S)
    else
      let builder =
        if use_timbuk then
          (module Automata.TimbukBuilder : Automata.AutomatonBuilder)
        else
          (module TimbukVataBuilder.Make : Automata.AutomatonBuilder)
      in
      if tc_synth then
        (module (TraceCompleteFTASynthesizer.Create(val builder))
          : Synthesizer.S)
      else
        (module (FTASynthesizer.Create(val builder))
          : Synthesizer.S)
  in
  let module Synthesizer = (val synth) in
  let e = Synthesizer.synth ~problem in
  print_endline (Expr.show e);
  if print_times then
    begin
      print_endline ("Intersection Time: " ^ (Float.to_string !Consts.isect_time));
      print_endline ("Minify Time: " ^ (Float.to_string !Consts.minify_time));
      print_endline ("Min-elt Time: " ^ (Float.to_string !Consts.min_elt_time));
    end

open MyStdLib.Command.Let_syntax
let param =
  MyStdLib.Command.basic ~summary:"..."
    [%map_open
      let input_spec  = anon ("input_spec" %: string)
      and use_myth   = flag "use-myth" no_arg ~doc:"Solve using the myth synthesis engine"
      and log   = flag "log" no_arg ~doc:"log process"
      and use_l2   = flag "use-l2" no_arg ~doc:"Solve using the l2 synthesis engine"
      and print_times   = flag "print-times" no_arg ~doc:"print the times to run various components"
      and tc_synth   = flag "tc-synth" no_arg ~doc:"use the FTA synthesizer with trace complete examples"
      and use_timbuk   = flag "use-timbuk" no_arg ~doc:"use the timbuk to synthesize"
      and print_mapping   = flag "print-mapping" no_arg ~doc:"print timbuk to vata mapping"
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
          print_times
          tc_synth
          use_timbuk
          print_mapping
    ]

let () =
  Core.Command.run
    param
