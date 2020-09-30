open MyStdLib

module TypeDS =
  DisjointSetWithSetDataOf
    (Type)
    (BoolModule)
    (struct
      type t = Type.t -> bool
      let v = (Option.is_some % Type.destruct_mu)
    end)
    (struct
      type t = bool -> bool -> bool
      let v = (||)
    end)

module TypeToValues = DictOf(Type)(ListOf(Value))
module VSet = SetOf(Value)

let get_states
    ~(problem:Problem.t)
  : unit =
  let (args_t,res_t) = problem.synth_type in
  let vs =
    List.concat_map
      ~f:(fun (vs,v) ->
          List.map2_exn
            ~f:(ValueTCIntegration.tc_val problem.tc)
            (v::vs)
            (res_t::args_t))
      problem.examples
  in
  let sub_vs =
    List.dedup_and_sort
      ~compare:ValueTCIntegration.Derivation.compare
      (List.concat_map
         ~f:ValueTCIntegration.Derivation.sub_derivations
         vs)
  in
  let all_types =
    List.dedup_and_sort ~compare:Type.compare
      (List.filter
         ~f:(Option.is_none % Type.destruct_arr)
         (List.concat_map
            ~f:(Typecheck.all_subtypes problem.tc)
            (res_t
             ::args_t
             @(List.map ~f:Type.mk_named (Context.keys problem.tc))
             @(Context.data problem.ec))))

  in
  let ds =
    TypeDS.create_from_list
      ~equiv:(Typecheck.type_equiv problem.tc)
      all_types
  in
  let sub_vs_mus =
    List.filter
      ~f:(fun d ->
          snd
            (TypeDS.find_representative
               ds
               (ValueTCIntegration.Derivation.get_type d)))
      sub_vs
  in
  let vs_ts =
    List.map
      ~f:(fun d ->
          (ValueTCIntegration.Derivation.get_value d
          ,TypeDS.find_representative ds (ValueTCIntegration.Derivation.get_type d)))
      sub_vs_mus
  in
  let d =
    List.fold
      ~f:(fun d (v,(t,_)) ->
          TypeToValues.insert_or_combine
            ~combiner:(@)
            d
            t
            [v])
      ~init:TypeToValues.empty
      vs_ts
  in
  let eval_context = problem.eval_context in
  let e_t =
    List.map
      ~f:(fun (i,e) ->
          let t = Context.find_exn problem.ec i in
          (i,e,Type.split_to_arg_list_result t))
      eval_context
  in
  let (d,_) =
    List.fold
      ~f:(fun (d,ts) _ ->
          List.fold
            ~f:(fun (dacc,ts) (i,e,(targs,t)) ->
                let args =
                  List.map
                    ~f:(TypeToValues.lookup_default
                          ~default:[]
                          d)
                    targs
                in
                let resultant =
                  combinations
                    args
                in
                let args_res =
                  List.map
                    ~f:(fun args ->
                        let e =
                          List.fold
                            ~f:(fun e a ->
                                Expr.mk_app
                                  e
                                  (Value.to_exp a))
                            ~init:e
                            args
                        in
                        let v =
                          Eval.evaluate_with_holes
                            ~eval_context
                            e
                        in
                        (args,v))
                    resultant
                in
                List.fold
                  ~f:(fun (dacc,ts) (args,res) ->
                      let ts = (i,args,res)::ts in
                      let dacc =
                        TypeToValues.insert_or_combine
                          ~combiner:(fun s1 s2 ->
                              List.dedup_and_sort
                                ~compare:Value.compare
                                (s1@s2))
                          dacc
                          t
                          [res]
                      in
                      (dacc,ts))
                  ~init:(dacc,ts)
                  args_res)
            ~init:(d,ts)
            e_t)
      ~init:(d,[])
      (range 0 2)
  in
  (*print_endline
    (string_of_list
       (string_of_triple
          Id.show
          (string_of_list Value.show)
          Value.show)
       (List.dedup_and_sort
          ~compare:(triple_compare Id.compare (List.compare Value.compare) Value.compare)
          ts));*)
  print_endline (TypeToValues.show d);
  ()

