open MyStdLib

let get_states
    ~(problem:Problem.t)
  : Problem.t =
  let all_example_terms =
    List.dedup_and_sort
      ~compare:Value.compare
      (List.concat_map
         ~f:(fun (vs,v) -> v::vs)
         problem.examples)
  in
  let _ =
    List.dedup_and_sort
      ~compare:Value.compare
      (List.concat_map ~f:Value.subvalues all_example_terms)
  in
  problem

