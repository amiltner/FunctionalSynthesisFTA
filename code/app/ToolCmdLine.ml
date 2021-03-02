open MyStdLib
open Tool
open Lang

let rec import_imports
    (acc:Problem.t_unprocessed)
  : Problem.t_unprocessed =
  begin match Problem.extract_file acc with
    | None -> acc
    | Some (fname,acc) ->
      let (news,newd) =
        Parser.imports_decls_start
          Lexer.token
          (Lexing.from_string
             (MyStdLib.SimpleFile.read_from_file ~fname))
      in
      let news = Problem.update_import_base news fname in
      import_imports
        (Problem.merge_unprocessed
           acc
           (news,newd))
  end

module Crazy = CrazyFTASynthesizer.Create(Automata.TimbukBuilder)
module VEQ = Synthesizers.VerifiedEquiv.Make(Synthesizers.IOSynth.OfPredSynth(Crazy))(QuickCheckVerifier.T)

let get_ioe_synthesizer
    ~(use_myth:bool)
    ~(use_l2:bool)
    ~(tc_synth:bool)
    ~(use_vata:bool)
  : (module Synthesizers.IOSynth.S) =
  let synth =
    if use_myth then
      (module MythSynthesisCaller : Synthesizers.IOSynth.S)
    else if use_l2 then
      (module L2SynthesisCaller : Synthesizers.IOSynth.S)
    else
      let builder =
        if use_vata then
          (module TimbukVataBuilder.Make : Automata.AutomatonBuilder)
        else
          (module Automata.TimbukBuilder : Automata.AutomatonBuilder)
      in
      (module Synthesizers.IOSynth.OfPredSynth(CrazyFTASynthesizer.Create(val builder)) : Synthesizers.IOSynth.S)
  in
  if tc_synth then
    (module Synthesizers.IOSynth.TCToNonTC(val synth) : Synthesizers.IOSynth.S)
  else
    synth


let synthesize_satisfying_verified_equiv
    ~(context:Context.t)
    ~(tin:Type.t)
    ~(tout:Type.t)
    ~(equiv:Value.t -> Value.t)
    ~(use_myth:bool)
    ~(use_l2:bool)
    ~(tc_synth:bool)
    ~(use_vata:bool)
  : Expr.t =
  let synth = get_ioe_synthesizer ~use_myth ~use_l2 ~tc_synth ~use_vata in
  let module S = Synthesizers.VerifiedEquiv.Make(val synth)(QuickCheckVerifier.T) in
  S.synth ~context ~tin ~tout equiv

let synthesize_satisfying_postcondition
    ~(context:Context.t)
    ~(tin:Type.t)
    ~(tout:Type.t)
    ~(post:Value.t -> Value.t -> bool)
    ~(use_myth:bool)
    ~(use_l2:bool)
    ~(tc_synth:bool)
    ~(use_vata:bool)
  : Expr.t =
  if use_myth then failwith "invalid synthesizer for postconditions";
  if use_l2 then failwith "invalid synthesizer for postconditions";
  if tc_synth then failwith "invalid synthesizer for postconditions";
  let synth =
    let builder =
      if use_vata then
        (module TimbukVataBuilder.Make : Automata.AutomatonBuilder)
      else
        (module Automata.TimbukBuilder : Automata.AutomatonBuilder)
    in
    (module CrazyFTASynthesizer.Create(val builder) : Synthesizers.PredicateSynth.S)
  in
  let module S = Synthesizers.VerifiedPredicate.Make(val synth)(EnumerativeVerifier.T) in
  S.synth ~context ~tin ~tout post

let synthesize_satisfying_ioes
    ~(context:Context.t)
    ~(tin:Type.t)
    ~(tout:Type.t)
    ~(ioes:(Value.t * Value.t) list)
    ~(use_myth:bool)
    ~(use_l2:bool)
    ~(tc_synth:bool)
    ~(use_vata:bool)
  : Expr.t =
  let synth = get_ioe_synthesizer ~use_myth ~use_l2 ~tc_synth ~use_vata in
  let module S = (val synth) in
  let sa = S.init ~context ~tin ~tout in
  snd (S.synth sa ioes)

let synthesize_solution
    ~(fname:string)
    ~(use_myth:bool)
    ~(use_l2:bool)
    ~(log:bool)
    ~(run_experiments:bool)
    ~(print_times:bool)
    ~(tc_synth:bool)
    ~(use_vata:bool)
    ~(print_mapping:bool)
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
  let p_unprocessed = Problem.update_all_import_bases p_unprocessed fname in
  let p_unprocessed = import_imports p_unprocessed in
  let problem = Problem.process p_unprocessed in
  (*print_endline (Expr.show (Crazy.simple_synth ~problem));*)
  (*let synth =
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
    let e = Synthesizer.synth ~problem in*)
  let e =
    begin match problem.spec with
      | IOEs ioes ->
        let context = Problem.extract_context problem in
        let (tin,tout) = problem.synth_type in
        synthesize_satisfying_ioes
          ~context
          ~tin
          ~tout
          ~ioes
          ~use_myth
          ~use_l2
          ~tc_synth
          ~use_vata
      | Post post ->
        let context = Problem.extract_context problem in
        let (tin,tout) = problem.synth_type in
        synthesize_satisfying_postcondition
          ~context
          ~tin
          ~tout
          ~post
          ~use_myth
          ~use_l2
          ~tc_synth
          ~use_vata
      | Equiv equiv ->
        let context = Problem.extract_context problem in
        let (tin,tout) = problem.synth_type in
        synthesize_satisfying_verified_equiv
          ~context
          ~tin
          ~tout
          ~equiv
          ~use_myth
          ~use_l2
          ~tc_synth
          ~use_vata
    end
  in
  if run_experiments then
    begin
      print_endline (Expr.show e);
      print_endline ";";
      print_endline (Float.to_string (Consts.total Consts.isect_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.max Consts.isect_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.total Consts.minify_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.max Consts.minify_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.total Consts.min_elt_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.max Consts.min_elt_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.total Consts.initial_creation_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.max Consts.initial_creation_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.total Consts.accepts_term_times));
      print_endline ";";
      print_endline (Float.to_string (Consts.max Consts.accepts_term_times);)
    end
  else
    begin
      print_endline (Expr.show e);
      if print_times then
        begin
          print_endline ("Total Intersection Time: " ^ (Float.to_string (Consts.total Consts.isect_times)));
          print_endline ("Max Intersection Time: " ^ (Float.to_string (Consts.max Consts.isect_times)));
          print_endline ("Total Minify Time: " ^ (Float.to_string (Consts.total Consts.minify_times)));
          print_endline ("Max Minify Time: " ^ (Float.to_string (Consts.max Consts.minify_times)));
          print_endline ("Total Min-elt Time: " ^ (Float.to_string (Consts.total Consts.min_elt_times)));
          print_endline ("Max Min-elt Time: " ^ (Float.to_string (Consts.max Consts.min_elt_times)));
          print_endline ("Total Initial Creation Time: " ^ (Float.to_string (Consts.total Consts.initial_creation_times)));
          print_endline ("Max Initial Creation Time: " ^ (Float.to_string (Consts.max Consts.initial_creation_times)));
          print_endline ("Total Accepts Term Time: " ^ (Float.to_string (Consts.total Consts.accepts_term_times)));
          print_endline ("Max Accepts Term Time: " ^ (Float.to_string (Consts.max Consts.accepts_term_times));)
        end
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
      and run_experiments   = flag "run-experiments" no_arg ~doc:"print the times to run various components"
      and tc_synth   = flag "tc-synth" no_arg ~doc:"use the FTA synthesizer with trace complete examples"
      and use_vata   = flag "use-vata" no_arg ~doc:"use vata to synthesize"
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
          ~fname:input_spec
          ~use_myth
          ~use_l2
          ~log
          ~print_times
          ~run_experiments
          ~tc_synth
          ~use_vata
          ~print_mapping
    ]

let () =
  Core.Command.run
    param
