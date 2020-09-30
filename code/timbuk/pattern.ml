module type ORDERED_FORMAT_TYPE = Symbol.ORDERED_FORMAT_TYPE

module type VARIABLE = sig
  include ORDERED_FORMAT_TYPE

  val product : t -> t -> t option
end

type position = Term.position

type ('sym, 'x) pattern =
  | Cons of 'sym * (('sym, 'x) pattern) list
  | Var of 'x

module type S = sig
  module Sym : Symbol.S
  module Var : VARIABLE

  type ('sym, 'x) abs_pattern = ('sym, 'x) pattern =
    | Cons of 'sym * (('sym, 'x) pattern) list
    | Var of 'x
  type term = Sym.t Term.term
  type t = (Sym.t, Var.t) pattern

  exception InvalidPosition of position * t

  val create : Sym.t -> t list -> t
  val of_term : term -> t
  val of_var : Var.t -> t
  val is_cons : t -> bool
  val is_var : t -> bool
  val normalized : t -> Var.t
  val subterm : position -> t -> t
  val subterm_opt : position -> t -> t option
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
  val fold : (Var.t -> 'a -> 'a) -> t -> 'a -> 'a
  val is_closed : t -> bool
  val for_all : (Var.t -> bool) -> t -> bool
  val apply : (Var.t -> t) -> t -> t
  val instanciate : (Var.t -> term) -> t -> term
  val as_term : t -> term
  val product : t -> t -> t option
  val print : t -> Format.formatter -> unit
  val print_var : (Var.t -> Format.formatter -> unit) -> t -> Format.formatter -> unit
end

module Make (F: Symbol.S) (X : VARIABLE) = struct
  module Sym = F
  module Var = X

  type ('sym, 'x) abs_pattern = ('sym, 'x) pattern =
    | Cons of 'sym * (('sym, 'x) pattern) list
    | Var of 'x
  type term = Sym.t Term.term
  type t = (Sym.t, Var.t) pattern

  exception InvalidPosition of position * t

  let create f l =
    if Sym.arity f = List.length l then
      Cons (f, l)
    else raise (Invalid_argument "symbol arity does not match list length")

  let rec of_term (Term.Term (f, l)) =
    Cons (f, List.map (of_term) l)

  let of_var x =
    Var x

  let is_cons = function
    | Cons _ -> true
    | _ -> false

  let is_var = function
    | Var _ -> true
    | _ -> false

  let normalized = function
    | Var x -> x
    | _ -> raise (Invalid_argument "not normalized.")

  let rec subterm_opt pos t =
    match pos, t with
    | Term.Subterm (i, pos), Cons (_, l) ->
      (match List.nth_opt l i with Some s -> subterm_opt pos s | None -> None)
    | Term.Root, _ -> Some t
    | _, _ -> None

  let subterm pos t =
    match subterm_opt pos t with
    | Some t -> t
    | None -> raise (InvalidPosition (pos, t))

  let rec compare a b =
    match a, b with
    | Var x, Var y -> Var.compare x y
    | Var _, _ -> 1
    | _, Var _ -> -1
    | Cons (fa, la), Cons (fb, lb) -> (* copy/paste from above *)
      let rec lex_order la lb = (* lexicographic order to compare subterms *)
        match la, lb with
        | [], [] -> 0 (* terms are equals *)
        | a::la, b::lb ->
          let c = compare a b in
          if c = 0 then lex_order la lb else c
        | _::_, [] -> -1
        | _, _ -> 1
      in
      let c = Sym.compare fa fb in (* first we compare the constructors... *)
      if c = 0 then lex_order la lb else c (* ...if there are equals, we compare the subterms. *)

  let rec equal a b =
    match a, b with
    | Var x, Var y -> Var.equal x y
    | Cons (fa, la), Cons (fb, lb) ->
      Sym.equal fa fb && List.for_all2 (fun ta tb -> equal ta tb) la lb
    | _, _ -> false

  let hash t = Hashtbl.hash t

  (* let variables t =
     let rec vars set = function
      | Cons (f, l) -> List.fold_left (vars) set l
      | Var x -> VarSet.add x set
     in vars (VarSet.empty) t *)

  let fold f t x =
    let table = Hashtbl.create 8 in
    let visit var =
      match Hashtbl.find_opt table var with
      | Some () -> false
      | None ->
        Hashtbl.add table var ();
        true
    in
    let rec do_fold t x =
      match t with
      | Cons (_, l) -> List.fold_right do_fold l x
      | Var var -> if visit var then f var x else x
    in
    do_fold t x

  let rec is_closed = function
    | Cons (_, l) -> List.for_all (is_closed) l
    | Var _ -> false

  let rec for_all f = function
    | Cons (_, l) -> List.for_all (for_all f) l
    | Var x -> f x

  let rec apply sigma = function
    | Cons (f, l) -> Cons (f, List.map (apply sigma) l)
    | Var x ->
      try sigma x with
      | Not_found -> Var x

  let rec instanciate sigma = function
    | Cons (f, l) -> Term.Term (f, List.map (instanciate sigma) l)
    | Var x -> sigma x

  let as_term t =
    instanciate (function _ -> raise (Invalid_argument "pattern is not a term")) t

  let rec product a b =
    match a, b with
    | Cons (fa, la), Cons (fb, lb) when Sym.compare fa fb = 0 ->
      let fold_product c d l = begin
        match l with
        | Some l ->
          begin
            match product c d with
            | Some p -> Some (p::l)
            | None -> None
          end
        | None -> None
      end in
      begin
        match List.fold_right2 (fold_product) la lb (Some []) with
        | Some l -> Some (Cons (fa, l))
        | None -> None
      end
    | Var x, Var y ->
      begin
        match Var.product x y with
        | Some z -> Some (Var z)
        | None -> None
      end
    | _ ->
      None

  let rec print_var pp_var t out =
    match t with
    | Cons (f, []) -> Sym.print f out
    | Cons (f, l) ->
      Format.fprintf out "%t(%t)" (Sym.print f) (Collections.List.print (print_var pp_var) ", " l)
    | Var x -> pp_var x out

  let print = print_var Var.print
end

module Ext (A : S) (B : S with module Sym = A.Sym) = struct
  let rec substitute sigma = function
    | A.Cons (f, l) -> B.Cons (f, List.map (substitute sigma) l)
    | A.Var x -> sigma x
end

module Product (A : S) (B : S with module Sym = A.Sym) (AB : S with module Sym = B.Sym) = struct
  let rec product mult a b =
    match a, b with
    | A.Cons (fa, la), B.Cons (fb, lb) when A.Sym.compare fa fb = 0 ->
      let fold_product c d l = begin
        match l with
        | Some l ->
          begin
            match product (mult) c d with
            | Some p -> Some (p::l)
            | None -> None
          end
        | None -> None
      end in
      begin
        match List.fold_right2 (fold_product) la lb (Some []) with
        | Some l -> Some (AB.Cons (fa, l))
        | None -> None
      end
    | A.Var x, B.Var y ->
      begin
        match mult x y with
        | Some z -> Some (AB.Var z)
        | None -> None
      end
    | _ ->
      None
end
