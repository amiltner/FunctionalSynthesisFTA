open MyStdLib
open Lang

module PredicateSynth =
struct
  module type S =
  sig
    type t
    val context : t -> Context.t
    val tin : t -> Type.t
    val tout : t -> Type.t

    val init :
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      t

    val synth :
      t ->
      Value.t list ->
      (Value.t -> Value.t -> bool) ->
      t * Expr.t
  end
end

module IOSynth =
struct
  module type S =
  sig
    type t
    val context : t -> Context.t
    val tin : t -> Type.t
    val tout : t -> Type.t

    val init :
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      t
    val synth :
      t -> (Value.t * Value.t) list -> t * Expr.t
  end

  module TCToNonTC(TC : S) : S = struct
    include TC

    let synth
        (acc:t)
        (ios:(Value.t * Value.t) list)
      : t * Expr.t =
      let all_inputs =
        List.dedup_and_sort
          ~compare:Value.compare
          (List.concat_map ~f:(Value.subvalues % fst) ios)
      in
      let all_ios =
        List.map
          ~f:(fun i ->
              begin match List.Assoc.find ~equal:Value.equal ios i with
                | None ->
                  (i,Option.value_exn (Value.of_type (tout acc)))
                | Some o -> (i,o)
              end)
          all_inputs
      in
      TC.synth acc all_ios
  end

  module OfPredSynth(PS : PredicateSynth.S) : S = struct
    include PS

    let synth
        (a:t)
        (ios:(Value.t * Value.t) list)
      : t * Expr.t =
      let pred =
        fun v1 v2 ->
          begin match List.Assoc.find ~equal:Value.equal ios v1 with
            | None -> true
            | Some v2' -> Value.equal v2 v2'
          end
      in
      let ins = List.map ~f:fst ios in
      PS.synth a ins pred
  end
end

module Verifier = struct
  module type S = sig
    val satisfies_post :
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      cand:Expr.t ->
      checker:(Value.t -> Value.t -> bool) ->
      Value.t option
  end
end

module VerifiedPredicate = struct
  module type S =
  sig
    val synth :
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      (Value.t -> Value.t -> bool) ->
      Expr.t

  end

  module Make(S : PredicateSynth.S)(V : Verifier.S) : S = struct
    let synth
        ~(context:Context.t)
        ~(tin:Type.t)
        ~(tout:Type.t)
        (checker:Value.t -> Value.t -> bool)
      : Expr.t =
      let rec synth_internal
          (sacc:S.t)
          (inputs:Value.t list)
        : Expr.t =
        let (sacc,cand) = S.synth sacc inputs checker in
        let cex_o = V.satisfies_post ~context ~tin ~tout ~cand ~checker in
        begin match cex_o with
          | None -> cand
          | Some cex -> synth_internal sacc (cex::inputs)
        end
      in
      synth_internal (S.init ~context ~tin ~tout) []
  end
end

module VerifiedEquiv = struct
  module type S =
  sig
    val synth :
      context:Context.t ->
      tin:Type.t ->
      tout:Type.t ->
      (Value.t -> Value.t) ->
      Expr.t
  end

  module Make(S : IOSynth.S)(V : Verifier.S) : S = struct
    let mk_checker
        (runner:Value.t -> Value.t)
        (vin:Value.t)
        (vout:Value.t)
      : bool =
      let vout_correct = runner vin in
      Value.equal vout vout_correct

    let synth
        ~(context:Context.t)
        ~(tin:Type.t)
        ~(tout:Type.t)
        (runner:Value.t -> Value.t)
      : Expr.t =
      let checker = mk_checker runner in
      let rec synth_internal
          (sacc:S.t)
          (ios:(Value.t * Value.t) list)
        : Expr.t =
        let (sacc,cand) = S.synth sacc ios in
        Consts.log (fun _ -> "Candidate Found: " ^ (Expr.show cand));
        let cex_o = V.satisfies_post ~context ~cand ~checker ~tin ~tout in
        begin match cex_o with
          | None -> cand
          | Some cex ->
            Consts.log (fun _ -> "CEx Found: " ^ (Value.show cex));
            let cex_out = runner cex in
            synth_internal sacc ((cex,cex_out)::ios)
        end
      in
      synth_internal (S.init ~context ~tin ~tout) []
  end
end
