open MyStdLib

open Typecheck

type t_unprocessed = Declaration.t list
                     * Type.t
                     * (Expr.t list * Expr.t) list
[@@deriving eq, hash, ord, show]

type t = {
  synth_type   : Type.t                          ;
  ec           : Context.Exprs.t                 ;
  tc           : Context.Types.t                 ;
  vc           : Context.Variants.t              ;
  examples     : ((Value.t list) * Value.t) list ;
  eval_context : (Id.t * Expr.t) list            ;
  unprocessed  : t_unprocessed                   ;
}
[@@deriving eq, hash, make, ord]


let extract_variants
    (t:Type.t)
    : (Context.Variants.key * Context.Variants.value) list =
  fst (Type.fold
         ~name_f:(fun i -> ([],Type.mk_named i))
         ~arr_f:(fun (vs1,t1) (vs2,t2) -> (vs1@vs2,Type.mk_arrow t1 t2))
         ~tuple_f:(fun vss_ts ->
                     let (vss,ts) = List.unzip vss_ts in
                     (List.concat vss, Type.mk_tuple ts))
        ~mu_f:(fun _ vs -> vs)
        ~variant_f:(fun ids_vss_ts ->
                      let (ids,vss_ts) = List.unzip ids_vss_ts in
                      let (vss,ts) = List.unzip vss_ts in
                      let ids_ts = List.zip_exn ids ts in
                      let ids_map = List.map ~f:(fun id -> (id,ids_ts)) ids in
                      (ids_map@(List.concat vss), Type.mk_variant ids_ts))
        t)

let process_decl_list
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (ds:Declaration.t list)
  : (Context.Exprs.t * Context.Types.t * Context.Variants.t * (Id.t * Expr.t) list) =
  fst
    (List.fold_left
       ~f:(fun ((new_ec,new_tc,new_vc,i_e),(ec,tc,vc)) decl ->
           Declaration.fold
             ~type_f:(fun i t ->
                 let all_variants = extract_variants t in
                 ((new_ec
                  ,Context.set new_tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Context.set vc ~key:k ~data:v)
                      ~init:new_vc
                      all_variants
                  ,i_e)
                 ,(ec
                  ,Context.set tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Context.set vc ~key:k ~data:v)
                      ~init:vc
                      all_variants))
               )
             ~expr_f:(fun i e ->
                 let t = typecheck_exp ec tc vc e in
                 ((Context.set new_ec ~key:i ~data:t
                  ,new_tc
                  ,new_vc
                  ,(i,e)::i_e)
                 ,(Context.set ec ~key:i ~data:t
                  ,tc
                  ,vc))
               )
             decl)
       ~init:(((Context.empty,Context.empty,Context.empty,[])
              ,(ec,tc,vc)))
       ds)

let process (unprocessed : t_unprocessed) : t =
  let (decs,synth_type,exs) = unprocessed in
  let (ec,tc,vc,i_e) =
    process_decl_list
      Context.empty
      Context.empty
      Context.empty
      decs
  in
  let eval_context =
    (*(List.concat_map
       ~f:(fun cts ->
           List.map
             ~f:(fun (c,t) -> (c, Expr.mk_func (Id.create "i",t) (Expr.Ctor (c, Expr.mk_var (Id.create "i")))))
             cts)
       (Context.data vc))
      @*) i_e
  in
  let examples =
    List.map
      ~f:(fun (es,e) ->
          let vs =
            List.map
              ~f:(Eval.evaluate_with_holes ~eval_context)
              es
          in
          let v =
            Eval.evaluate_with_holes
            ~eval_context
            e
          in
          (vs,v))
      exs
  in
  make
    ~ec
    ~tc
    ~vc
    ~eval_context
    ~unprocessed
    ~synth_type
    ~examples
    ()
