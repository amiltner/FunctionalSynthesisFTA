type cmp =
  | LT
  | EQ
  | GT

let compare =
  fix (compare : nat -> nat -> cmp) =
    fun (x1 : nat) ->
      fun (x2 : nat) ->
        match x1 binding x1 with
        | O -> (match x2 binding x2 with
                | O -> EQ
                | S -> LT)
        | S -> (match x2 binding x2 with
                | O -> GT
                | S -> compare x1 x2)
;;