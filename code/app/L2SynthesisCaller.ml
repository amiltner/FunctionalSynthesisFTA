open MyStdLib
open Tool
open MythSynthesisCaller

let synth
  ~(problem:Problem.t)
  : Expr.t =
  let (_,examples,_) = DSToMyth.convert_problem_examples_type_to_myth problem in
    let rec print_examples e =
    match e with
    | []      -> ()
    | x :: [] -> let y = Myth.Pp.pp_exp x in print_endline ("        \"" ^ y ^ "\"")
  | x :: l  -> let y = Myth.Pp.pp_exp x in print_endline ("        \"" ^ y ^ "\","); print_examples l
  in
    let _ = print_endline "{";
    print_endline "  \"name\": \"f\",";
    print_endline "  \"description\": \"\",";
    print_endline "  \"kind\": \"examples\",";
    print_endline "  \"contents\": {";
    print_endline "    \"examples\": [";
    print_examples examples;
    print_endline "    ],";
    print_endline "    \"background\": []";
    print_endline "  }";
  print_endline "}" in
  Expr.Tuple []
