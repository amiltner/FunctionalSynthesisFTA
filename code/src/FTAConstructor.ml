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
module VSet = SetOf(Value)

module A =
struct
  module Symb = struct
    type t = (Id.t * int)
    [@@deriving eq, hash, ord, show]

    let print a b = pp b a

    let arity = snd
  end

  module St = struct
    type t =
      | Vals of (Value.t * Value.t) list * Type.t
      | Top
    [@@deriving eq, hash, ord, show]

    let print a b = pp b a

    let product a b =
      begin match (a,b) with
        | (Vals (avs,at), Vals (bvs,bt)) ->
          if Type.equal at bt then
            Some (Vals ((avs@bvs),at))
          else
            None
        | (Top, _) -> Some b
        | (_, Top) -> Some a
      end

    let compare x y = -(compare x y)
  end

  module Lb = struct
    include UnitModule

    let print a b = pp b a

    let product _ _ = Some ()
  end

  include Timbuk.Automaton.Make(Symb)(St)(Lb)

  let rec boundterm_to_exp
      ((bt,_):BoundTerm.t)
    : Expr.t =
    begin match bt with
      | BoundTerm.Term (s,bts) ->
        List.fold
          ~f:(fun acc bt ->
              Expr.mk_app
                acc
                (boundterm_to_exp bt))
          ~init:(Expr.mk_var (fst s))
          bts
      | _ -> failwith "ah"
    end
end

(*module TypeToStates = DictOf(Type)(ListOf(A.St))*)
module TypeToValues = DictOf(Type)(ListOf(Value))

let call_thing
  ()
  : unit =
  (*let a = A.create () in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "init", 0),
         []))
      ()
      (Base (Value.Tuple []))
      a
  in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "init", 0),
          []))
      ()
      (Base (Value.Tuple [Value.Tuple []]))
      a
  in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "mergit", 1),
          [A.Configuration.Var (Base (Value.Tuple []))]))
      ()
      (Base (Value.Tuple [Value.Tuple []]))
      a
  in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "mergit", 1),
          [A.Configuration.Var (Base (Value.Tuple [Value.Tuple []]))]))
      ()
      (Base (Value.Tuple [Value.Tuple []]))
      a
  in
  let a =
    A.add_final_state
      (Base (Value.Tuple []))
      a
  in
  let a =
    A.add_final_state
      (Base (Value.Tuple [Value.Tuple []]))
      a
  in
  print_endline "Before det";
  print_endline
    (A.print
       a
       Format.str_formatter;
     Format.flush_str_formatter ());
  (*let b =
    A.inter
      (fun () () -> ())
      a
      b
    in*)
  (*print_endline
    (A.print
       b
       Format.str_formatter;
     Format.flush_str_formatter ());*)
  let a =
    A.determinise
      (fun s ->
         begin match A.StateSet.elements s with
           | [a] -> a
           | [a;b] -> A.St.Pair (a,b)
           | _ -> failwith "ah"
         end)
      a
  in
  print_endline "After det";
  print_endline
    (A.print
       a
       Format.str_formatter;
     Format.flush_str_formatter ());
  let a =
    A.minimalise
      a
  in
  print_endline "After min";
  print_endline
    (A.print
       a
       Format.str_formatter;
     Format.flush_str_formatter ());
  print_endline "And bound term";
  print_endline
    (A.BoundTerm.print
       (A.pick_term ~smallest:true a)
       Format.str_formatter;
     Format.flush_str_formatter ());
  (*print_endline
    (A.BoundTerm.print
       (A.pick_term b)
       Format.str_formatter;
     Format.flush_str_formatter ());*)
  (*A.St.print
    ""
    Format.std_formatter*);
  (*val add_transition : ?hook:hook -> Configuration.t -> Label.t -> State.t -> t -> t
    module Configuration : Pattern.S with type Sym.t = Sym.t and type Var.t = State.t*)*)
  ()

(*type t =
  {
    a  : A.t            ;
    d  : TypeToStates.t ;
    ds : TypeDS.t       ;
  }*)

(*let initialize_types_from_type_space
    ~(problem:Problem.t)
    (ts:Type.t list)
  : TypeDS.t =
  let all_types =
    List.dedup_and_sort ~compare:Type.compare
      (List.filter
         ~f:(Option.is_none % Type.destruct_arr)
         (List.concat_map
            ~f:(Typecheck.all_subtypes problem.tc)
            ts))

  in
  TypeDS.create_from_list
    ~equiv:(Typecheck.type_equiv problem.tc)
    all_types

let construct_from_type_space_and_value_space
    ~(problem:Problem.t)
    (ts:Type.t list)
    (vs_ts:(Value.t * Type.t) list)
    (input_type:Type.t)
    (output_type:Type.t)
    (inputs:Value.t list)
    (output_validator:Value.t -> bool)
  : t =
  let ds =
    initialize_types_from_type_space
      ~problem
      ts
  in
  let vs_ts =
    List.map
      ~f:(fun (v,t) -> (v,fst (TypeDS.find_representative ds t)))
      vs_ts
  in
  let d =
    List.fold
      ~f:(fun d (v,t) ->
          List.fold
            ~f:(fun d i ->
                TypeToStates.insert_or_combine
                  ~combiner:(@)
                  d
                  t
                  [A.St.Vals ([(i,v)],t)])
            ~init:d
            inputs)
      ~init:TypeToStates.empty
      vs_ts
  in
  let a = A.empty in
  let a =
    List.fold
      ~f:(fun a va ->
          A.add_transition
            (A.Configuration.Cons
               ((Id.create "x", 0)
               ,[]))
            ()
            (A.St.Vals ([(va,va)],input_type))
            a)
      ~init:a
      inputs
  in
  {
    a  ;
    d  ;
    ds ;
  }

let update_from_conversions
    (conversions:(Id.t * Expr.t * (Type.t list) * Type.t) list)
    (a:t)
  : t =
  let (d,ivv) =
    List.fold
      ~f:(fun (dacc,ts) (i,e,targs,t) ->
          let t = fst (TypeDS.find_representative a.ds t) in
          let args =
            List.map
              ~f:(fun t ->
                  let t = fst (TypeDS.find_representative a.ds t) in
                  List.map
                    ~f:(fun x -> (x,t))
                    (TypeToStates.lookup_default
                       ~default:[]
                       a.d
                       t))
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
                      ~f:(fun e (a,_) ->
                          begin match a with
                            | A.St.Vals ([vin,vout],_) ->
                              
                            | _ -> failwith "shouldnt happen"
                              let outputs =
                                List.map
                                  ~f:(fun (vx,vres) ->
                                      let e =
                                        Expr.mk_app
                                          e
                                          (Value.to_exp)
                                      (vx,)
                                    )
                              in
                          List.map
                            ~f:(fun a ->
                              )
                          Expr.mk_app
                            e
                            (Value.to_exp a))
                      ~init:e
                      args
                  in
                  let v = Eval.evaluate e in
                  (args,v))
              resultant
          in
          List.fold
            ~f:(fun (dacc,ts) (args,res) ->
                let ts = (i,args,res,t)::ts in
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
      ~init:(a.d,[])
      conversions
  in
  let ivv = List.dedup_and_sort ~compare:(quad_compare Id.compare (compare_list ~cmp:(pair_compare Value.compare Type.compare)) Value.compare Type.compare) ivv in
  let a =
    List.fold
      ~f:(fun a (i,vs,v,t) ->
          A.StateSet.fold
            (fun varg a ->
                A.add_transition
                  (A.Configuration.Cons
                     ((i, (List.length vs))
                     ,List.map ~f:(fun (v,t) -> A.Configuration.Var (A.St.Vals ([(varg,v)],t))) vs))
                  ()
                  (A.St.Vals ([(varg,v)],t))
                  a)
            (A.states a)
            a)
      ~init:a
      ivv
  in
  failwith "ah"*)

let initialize_types_from_type_space
    ~(problem:Problem.t)
    (ts:Type.t list)
  : TypeDS.t =
  let all_types =
    List.dedup_and_sort ~compare:Type.compare
      (List.filter
         ~f:(Option.is_none % Type.destruct_arr)
         (List.concat_map
            ~f:(Typecheck.all_subtypes problem.tc)
            ts))

  in
  TypeDS.create_from_list
    ~equiv:(Typecheck.type_equiv problem.tc)
    all_types

let get_states
    ~(problem:Problem.t)
    : unit =
    let (args_t,res_t) = problem.synth_type in
    let ds =
      initialize_types_from_type_space
        ~problem
        ([res_t;args_t]
         @(List.map ~f:Type.mk_named (Context.keys problem.tc))
         @(Context.data problem.ec))
    in
    let vs =
      List.concat_map
      ~f:(fun (vs,v) ->
          List.map2_exn
            ~f:(ValueTCIntegration.tc_val problem.tc)
            ([v;vs])
            ([res_t;args_t]))
      problem.examples
  in
  let sub_vs =
    List.dedup_and_sort
      ~compare:ValueTCIntegration.Derivation.compare
      (List.concat_map
         ~f:ValueTCIntegration.Derivation.sub_derivations
         vs)
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
          ,fst (TypeDS.find_representative ds (ValueTCIntegration.Derivation.get_type d))))
      sub_vs_mus
  in
  let d =
    List.fold
      ~f:(fun d (v,t) ->
          TypeToValues.insert_or_combine
            ~combiner:(@)
            d
            t
            [v])
      ~init:TypeToValues.empty
      vs_ts
  in
  let relevant_vs =
    TypeToValues.lookup_exn
      d
      args_t
  in
  let eval_context = problem.eval_context in
  let e_t =
    List.map
      ~f:(fun (i,e) ->
          let t = Context.find_exn problem.ec i in
          (i,e,Type.split_to_arg_list_result t))
      eval_context
  in
  let (_,ivv) =
    List.fold
      ~f:(fun (d,ts) _ ->
          List.fold
            ~f:(fun (dacc,ts) (i,e,(targs,t)) ->
                let t = fst (TypeDS.find_representative ds t) in
                let args =
                  List.map
                    ~f:(fun t ->
                        let t = fst (TypeDS.find_representative ds t) in
                        List.map
                          ~f:(fun x -> (x,t))
                          (TypeToValues.lookup_default
                             ~default:[]
                             d
                             t))
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
                            ~f:(fun e (a,_) ->
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
                      let ts = (i,args,res,t)::ts in
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
  let ivv = List.dedup_and_sort ~compare:(quad_compare Id.compare (compare_list ~cmp:(pair_compare Value.compare Type.compare)) Value.compare Type.compare) ivv in
  let a = A.create () in
  let a =
    List.fold
      ~f:(fun a (i,vs,v,t) ->
          List.fold
            ~f:(fun a varg ->
                A.add_transition
                  (A.Configuration.Cons
                     ((i, (List.length vs))
                     ,List.map ~f:(fun (v,t) -> A.Configuration.Var (A.St.Vals ([(varg,v)],t))) vs))
                  ()
                  (A.St.Vals ([(varg,v)],t))
                  a)
            ~init:a
            relevant_vs)
      ~init:a
    ivv
  in
  let a =
    List.fold
      ~f:(fun a va ->
          A.add_transition
            (A.Configuration.Cons
               ((Id.create "x", 0)
               ,[]))
            ()
            (A.St.Vals ([(va,va)],res_t))
            a)
      ~init:a
      relevant_vs
  in
  let top =
    A.St.Top
  in
  let top_var = A.Configuration.Var top in
  let a =
    Context.fold
      ~f:(fun ~key ~data a ->
          let len = List.length (fst (Type.split_to_arg_list_result data)) in
          A.add_transition
            (A.Configuration.Cons
               ((key, len)
               ,List.init len ~f:(func_of top_var)))
            ()
            top
            a)
      ~init:a
      problem.ec
  in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "ifthenelse", 3)
         ,[top_var;top_var;top_var]))
      ()
      top
      a
  in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "let-in", 2)
         ,[top_var;top_var]))
      ()
      top
      a
  in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "rec-call", 1)
         ,[top_var]))
      ()
      top
      a
  in
  let a =
    A.add_transition
      (A.Configuration.Cons
         ((Id.create "x", 0)
         ,[]))
      ()
      top
      a
  in
  let a =
    A.StateSet.fold2
      (fun s1 s2 acc ->
         begin match (s1,s2) with
           | (Vals ([v11,v12],_), Vals ([v21,v22],t)) ->
             if List.mem
                 ~equal:(fun ex1 ex2 ->
                     is_equal
                       (pair_compare
                          Value.compare
                          Value.compare
                          ex1
                          ex2))
                 problem.examples
                 (v21,v22) && (Value.equal v12 v21)
                && List.mem ~equal:Value.equal (Value.strict_subvalues v11) v12
             then
               A.add_transition
                 (A.Configuration.Cons
                    ((Id.create "let-in", 2)
                    ,[A.Configuration.Var s1
                     ;A.Configuration.Var s2]))
                 ()
                 (Vals ([v11,v22],t))
                 acc
             else
               acc
           | _ -> acc
         end)
      (A.states a)
      (A.states a)
      a
  in
  let a =
    A.StateSet.fold
      (fun s a ->
         begin match s with
           | Top -> a
           | Vals ([(i,_)],_) ->
             let a =
               A.add_transition
                 (A.Configuration.Cons
                    ((Id.create "ifthenelse", 3)
                    ,[A.Configuration.Var (A.St.Vals ([(i,Value.true_val)],fst (TypeDS.find_representative ds Type._bool)))
                     ;A.Configuration.Var s
                     ;top_var]))
                 ()
                 s
                 a
             in
             let a =
               A.add_transition
                 (A.Configuration.Cons
                    ((Id.create "ifthenelse", 3)
                    ,[A.Configuration.Var (A.St.Vals ([(i,Value.false_val)],fst (TypeDS.find_representative ds Type._bool)))
                     ;top_var
                     ;A.Configuration.Var s]))
                 ()
                 s
                 a
             in
             a
           | _ -> failwith "invalid"
         end)
      (A.states a)
      a
  in
  let astart = a in
  let _ = astart in
  (*A.StateMap.iter
    (fun _ c ->
       print_endline (print_to_string (A.LabeledConfigurationSet.print A.LabeledConfiguration.print "\nNEXT\n") c))
    (A.configurations_for_states a);*)
  (*print_endline "hii";*)
  let ats =
    List.map
      ~f:(fun (ins,out) ->
          (*print_endline "hiyo";*)
          let inp = ins in
          let a =
            (A.add_final_state
               (A.St.Vals ([(inp,out)],res_t))
               a)
          in
          let a = A.prune_useless a in
          a
        )
      problem.examples
  in
  (*List.iter
    ~f:(fun a ->
        print_endline "BEGIN";
        (*A.StateSet.print (A.St.print) " ;\n\n " (A.states a) Format.str_formatter; print_endline (Format.flush_str_formatter ()); print_endline "end\n\n\n";*)
        print_endline (print_to_string A.print a);
          print_endline "END"
      )
    ats;*)
  print_endline "begin stateset";
  print_endline "end stateset";
  (*let a = List.hd_exn ats in*)
    print_endline "hi";
  (*List.iter ~f:(fun at -> print_endline (string_of_int  (A.state_count at))) ats;
    List.iter ~f:(fun at -> print_endline (string_of_int  (A.fold_transitions (fun _ _ _ x -> x+1) at 0))) ats;*)


  (*List.iter
    ~f:(fun a ->
  A.fold_transitions
    (fun c _ s _ ->
       print_endline "Configuration";
       print_endline
         (print_to_string
            A.Configuration.print
            c);
       print_endline "EndState";
       print_endline
         (print_to_string
            A.St.print
            s);
       print_endline "\n\n\n"
    )
    a
    ();

      print_endline "\n\n\n THAT WAS ONE OF THEM")
    ats;*)
  (*print_endline "end\n\n\n";*)
  (*let t s ts =
    Timbuk.Term.Term
      ((Id.create s, List.length ts)
      ,ts)
  in
  let bool_type = fst (TypeDS.find_representative ds Type._bool) in
  let nat_type = fst (TypeDS.find_representative ds Type._nat) in
  let _ = nat_type in
  let _ = bool_type in
  let correct_solution =
    t "ifthenelse"
      [t "nat_eq"
         [t "nat_succ"
            [t "x" []]
         ;t "nat_succ"
             [t "nat_z" []]]
      ;t "x" []
      ;t "nat_succ"
          [t "nat_succ"
             [t "nat_z" []]]]
  in
  (*print_endline (print_to_string A.print a);*)
  print_endline "THIS IS WHAT IT IS";
  print_endline (string_of_bool (A.recognizes correct_solution (List.hd_exn (List.tl_exn ats))));
  print_endline
    (string_of_bool
       (A.recognizes_in
          (A.St.Vals ([(Value.num_val 1,Value.num_val 2)],nat_type))
          (correct_solution)
          (List.hd_exn (List.tl_exn ats))));
    print_endline "THIS IS WHAT IT IS!";*)
  (*print_endline
    (A.states_for_configuration
       (A.Configuration.Cons (Id.create "ifthenelse", []))
    )*)


  let a =
    fold_on_head_exn
      ~f:(fun x y ->

          (*A.StateMap.iter
            (fun _ c ->
               print_endline (print_to_string (A.LabeledConfigurationSet.print A.LabeledConfiguration.print "\nNEXT\n") c))
            (A.configurations_for_states x);
          *)

          print_endline (string_of_int (A.state_count x));
          print_endline (string_of_int (A.state_count y));
          print_endline "start my inter"; let x = A.prune_useless (A.inter (fun _ _ -> ()) x y) in
           (*A.StateSet.print (A.St.print) " ;\n\n " (A.states x) Format.str_formatter; print_endline (Format.flush_str_formatter ());*)
           (*A.fold_transitions
             (fun c _ s _ ->
                print_endline "Configuration";
                print_endline
                  (print_to_string
                     A.Configuration.print
                     c);
                print_endline "EndState";
                print_endline
                  (print_to_string
                     A.St.print
                     s);
                print_endline "\n\n\n"
             )
             a
             ();*)
           x
         )
      ats
  in
  print_endline "end my inter";
  (*let update_fta a s =
    let ps = A.state_parents s a in
    let bad_transisions =
      List.filter
        ~f:(fun c ->
            begin match c with
              | (A.Configuration.Cons
                   ((id,2),[A.Configuration.Var _;A.Configuration.Var s2]))
                when Id.equal id (Id.create "let-in")
                  && A.St.equal s2 s ->
                true
              | _ -> false
            end)
        (A.ConfigurationSet.elements ps)
    in
    let (a,csls) =
      List.fold
        ~f:(fun (a,csls) c ->
            let ps =
              A.ConfigurationMap.find
                c
                (A.states_for_configurations a)
            in
            let (a,sls) =
              A.LabeledStateSet.fold
                (fun (s,l) (a,sls) ->
                   let a =
                     A.remove_transition
                       c
                       ()
                       s
                       a
                   in
                   let sls =
                     (s,l)::sls
                   in
                   (a,sls))
                ps
                (a,[])
            in
            let csls =
              (c,sls)::csls
            in
            (a,csls))
        ~init:(a,[])
        bad_transisions
    in
    List.fold
      ~f:(fun a (c,sls) ->
          List.fold
            ~f:(fun a (s,l) ->
                begin match c with
                  | (A.Configuration.Cons
                       ((id,2),[A.Configuration.Var s1;A.Configuration.Var _]))
                    when Id.equal id (Id.create "let-in") ->
                    let new_c =
                      A.Configuration.Cons
                        ((Id.create "rec-call",1),[A.Configuration.Var s1])
                    in
                    A.add_transition
                      new_c
                      l
                      s
                      a
                  | _ -> failwith "shouldnt happen"
                end)
            ~init:a
            sls
          )
      ~init:a
      csls
(*
    A.remove
    let _ = s in
    a*)
    in*)
  (*let rec get_all_recursions a =
    print_endline "looking";
    print_endline @$ Expr.show (A.boundterm_to_exp (A.pick_term a));
    print_endline "found";
    let candidates =
      List.filter
        ~f:(fun s ->
            let ps = A.state_parents s a in
            (not (A.St.equal s top)) &&
            A.ConfigurationSet.exists
              (fun c ->
                 begin match c with
                   | (A.Configuration.Cons
                        ((id,2),[A.Configuration.Var _;A.Configuration.Var s2]))
                     when Id.equal id (Id.create "let-in")
                       && A.St.equal s2 s ->
                     let _ = s2 in
                     true
                   | _ -> false
                 end)
              ps)
        (A.StateSet.elements (A.states a))
    in*)
    (*A.StateMap.iter
      (fun _ c ->
         print_endline (print_to_string (A.LabeledConfigurationSet.print A.LabeledConfiguration.print "\nNEXT\n") c))
      (A.configurations_for_states a);*)
    (*let ftas =
      List.concat_map
        ~f:(get_all_recursions % (update_fta a))
        candidates
    in
    a::ftas
      in*)
  (*let get_all_recursions' a =
    print_endline @$ Expr.show (A.boundterm_to_exp (A.pick_term a));
    let candidates =
      List.filter
        ~f:(fun s ->
            let ps = A.state_parents s a in
            (not (A.St.equal s top)) &&
            A.ConfigurationSet.exists
              (fun c ->
                 begin match c with
                   | (A.Configuration.Cons
                        ((id,2),[A.Configuration.Var _;A.Configuration.Var s2]))
                     when Id.equal id (Id.create "let-in")
                       && A.St.equal s2 s ->
                     let _ = s2 in
                     true
                   | _ -> false
                 end)
              ps)
        (A.StateSet.elements (A.states a))
    in
    List.fold
      ~f:(update_fta)
      ~init:a
      candidates
    in*)
  (*print_endline "rvs begin";
  let rvs =
    A.reachable_values a
  in
  (*print_endline "disgintuished";
  let bool_type = fst (TypeDS.find_representative ds Type._bool) in
  let s =
    A.St.Vals
      ([(Value.num_val 0, Value.true_val)
       ;(Value.num_val 1, Value.false_val)
       ;(Value.num_val 2, Value.false_val)],bool_type)
  in
  print_endline "State:";
  print_endline (A.St.show s);
  let bts = A.StateMap.find s rvs in
  print_endline "Min:";
  print_endline (Expr.show (A.boundterm_to_exp bts));
  print_endline "\n\n";
    print_endline "disgintuishedend ";*)
  A.StateSet.iter
    (fun s ->
       print_endline "State:";
       print_endline (A.St.show s);
       let bts = A.StateMap.find s rvs in
       print_endline "Min:";
       print_endline (Expr.show (A.boundterm_to_exp bts));
       print_endline "\n\n")
    (A.final_states a);*)
  print_endline "BEGIN FINALS";
  (A.StateSet.iter (fun _ -> print_endline "beep") (A.final_states a););
  print_endline "END FINALS";



  let e = A.boundterm_to_exp (A.pick_term a (*get_all_recursions' a*)) in
  print_endline (Expr.show e);
  (*let exs =
    List.filter_map
      ~f:(fun r ->
          print_endline "yo";
          Option.map ~f:(fun a ->
            let e = A.boundterm_to_exp a in
            print_endline (Expr.show e); e) (A.pick_term_opt r))
      (get_all_recursions a)
  in
  List.iter
    ~f:(fun e ->
        print_endline "Expr";
        print_endline (Expr.show e);
        print_endline "\n\n")
    exs;
  print_endline (string_of_int (List.length exs));
  let min =
    Option.value_exn
      (List.min_elt
         ~compare:(fun i j ->
             Int.compare (Expr.size i) (Expr.size j))
         exs)
  in
    print_endline (Expr.show min);*)
  (*print_endline (print_to_string A.print a);*)
  (*let a =
    List.fold
      ~f:(fun a v ->
          A.add_final_state
            (A.St.Base v)
            a)
      ~init:a
      (List.map ~f:snd (List.tl_exn problem.examples))
    in*)
    (*print_endline @$ string_of_int (A.state_count a);
      print_endline (string_of_int  (A.fold_transitions (fun _ _ _ x -> x+1) a 0)) ;
    print_endline
      (A.BoundTerm.print
         (A.pick_term a)
         Format.str_formatter;
       Format.flush_str_formatter ());*)
  print_endline
   (Expr.show
      (A.boundterm_to_exp   (A.pick_term a)));

  (*let bts =
    List.map
      ~f:(fun s ->
          A.StateMap.find s rvs)
      (A.StateSet.elements (A.final_states a))
  in
  List.iter
    ~f:(fun bts ->
        print_endline @$ Expr.show (A.boundterm_to_exp bts))
    bts;*)

(*
    print_endline "here we start";
    print_endline
      (print_to_string A.print a);*)

