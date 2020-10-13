open Collections
open Timbuk
open TimbukSolving

let log_src = Logs.Src.create "timbuk.typing.factorizer"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type S = sig
  module Aut : Automaton.S
  module Partition : Set.S with type elt = Aut.StateSet.t

  val factorize : (Aut.Sym.t * Aut.State.t list * Aut.State.t) -> Partition.t -> (Aut.State.t -> Aut.State.t -> bool) -> Aut.t -> (Partition.t list) option
end

module Make (Aut : Automaton.S) (P : Set.S with type elt = Aut.StateSet.t) (Solver : Solver.S with type Var.t = Aut.State.t) = struct
  module Aut = Aut
  module Partition = P

  let fold_expected_confs (f, l, _) has_simple_type aut func expected_partition x =
    let has_simple_type a b =
      if has_simple_type a b then true else begin
        (* Log.debug (fun m -> m "type %t is NOT a refinement of %t" (Aut.State.print b) (Aut.State.print a)); *)
        false
      end
    in
    Partition.fold (
      fun expected_ty x ->
        Aut.StateSet.fold (
          fun q x ->
            begin
              let expected_confs = Aut.configurations_for_state q aut in
              Aut.LabeledConfigurationSet.fold (
                fun (conf, _) x ->
                  match conf with
                  | Aut.Configuration.Cons (f', l') when Aut.Sym.equal f' f ->
                    let l' = List.map Aut.Configuration.normalized l' in
                    if List.for_all2 has_simple_type l l' then
                      func expected_ty q l' x
                    else x
                  | _ -> x
              ) expected_confs x
            end
        ) expected_ty x
    ) expected_partition x

  let init_solver f_sig partition has_simple_type aut =
    let (f, l, _) = f_sig in
    let table = Hashtbl.create 8 in (* simple type -> refined types *)
    let reverse_table = Hashtbl.create 8 in (* refined type -> simple type *)
    let register_simple_ty refined_q q =
      let simple_tys = match Hashtbl.find_opt reverse_table refined_q with
        | Some simple_tys ->
          Aut.StateSet.add q simple_tys
        | None ->
          Aut.StateSet.singleton q
      in
      Hashtbl.replace reverse_table refined_q simple_tys
    in
    (* For each expected configuration (f q1.1 ... q1.n) *)
    fold_expected_confs f_sig has_simple_type aut (
      fun ty1 _ l1 (solver : Solver.t) ->
        begin
          let solver = List.fold_right (
              fun q solver ->
                Solver.declare q solver
            ) l1 solver
          in
          List.iter2 (
            fun q refined_q ->
              register_simple_ty refined_q q;
              match Hashtbl.find_opt table q with
              | Some refined_states ->
                Hashtbl.replace table q (Aut.StateSet.add refined_q refined_states)
              | None ->
                Hashtbl.replace table q (Aut.StateSet.singleton refined_q)
          ) l l1;
          (* For each expected configuration of different expected type (f q2.1 ... q2.n) *)
          let partition_without_ty1 = Partition.remove ty1 partition in
          fold_expected_confs f_sig has_simple_type aut (
            fun _ty2 _ l2 (solver : Solver.t) -> (* ty1 != ty2 by construction. *)
              begin
                (* We must not merge types in a way in which configurations may be mistaken. *)
                (* So for the two configurations (f q1.1 ... q1.n) and (f q2.1 ... q2.n),
                   We must have q1.1 != q2.1 \/ ... \/ q1.n != q2.n. *)
                let new_constraint =
                  Solver.Or (
                    List.map2 (
                      fun q1 q2 ->
                        Solver.Neq (Solver.Variable q1, Solver.Variable q2)
                    ) l1 l2
                  )
                in
                Solver.add new_constraint solver
              end
          ) partition_without_ty1 solver
        end
    ) partition (Solver.create ()), table, reverse_table

  let factorize (f, l, ty) partition has_simple_type aut =
    (* Log.debug (fun m -> m "factorize: %t(%t) : %t@." (Aut.Sym.print f) (List.print Aut.State.print ", " l) (Aut.State.print ty)); *)
    (* Log.debug (fun m -> m "factorize with:\n%t@." (Aut.print aut)); *)
    let solver, table, reverse_table = init_solver (f, l, ty) partition has_simple_type aut in
    match Solver.solve solver with
    | Solver.Sat model ->
      begin
        let refined_table = Hashtbl.create 8 in (* model value -> refined types *)
        (* Log.debug (fun m -> m "model:"); *)
        Solver.Model.fold (
          fun refined_q x () ->
            let simple_tys = Hashtbl.find reverse_table refined_q in
            Aut.StateSet.iter (
              function simple_ty ->
                (* Log.debug (fun m -> m "model binding: %t : %t -> %d" (Aut.State.print refined_q) (Aut.State.print simple_ty) x); *)
                let states = match Hashtbl.find_opt refined_table (x, simple_ty) with
                  | Some states ->
                    Aut.StateSet.add refined_q states
                  | None ->
                    Aut.StateSet.singleton refined_q
                in
                Hashtbl.replace refined_table (x, simple_ty) states
            ) simple_tys;
        ) model ();
        try
          let factorized_l = List.map (
              function simple_ty ->
                (* Log.debug (fun m -> m "simple ty: %t" (Aut.State.print simple_ty)); *)
                let refined_states = Hashtbl.find table simple_ty in
                (* Log.debug (fun m -> m "refined states: %t@." (Aut.StateSet.print Aut.State.print ", " refined_states)); *)
                Aut.StateSet.fold (
                  fun refined_q types ->
                    (* Log.debug (fun m -> m "refined_q: %t@." (Aut.State.print refined_q)); *)
                    let x = Solver.Model.find refined_q model in
                    (* Log.debug (fun m -> m "x: %d@." x); *)
                    let ty = Hashtbl.find refined_table (x, simple_ty) in
                    (* Log.debug (fun m -> m "ty: %t@." (Aut.StateSet.print Aut.State.print ", " ty)); *)
                    Partition.add ty types
                ) refined_states Partition.empty
            ) l
          in
          Some factorized_l
        with
        | Not_found ->
          (* debug "not found@."; *)
          None
      end
    | _ -> None (* failwith "unable to factorize expected confs" *)
end
