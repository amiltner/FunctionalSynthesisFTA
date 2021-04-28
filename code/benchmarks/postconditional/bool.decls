type bool =
  | False
  | True

let bool_not =
  fun (b:bool) ->
    (match b with
    | True -> False
    | False -> True)
;;

let bool_eq =
  fun (b1:bool) ->
    fun (b2:bool) ->
      (match b1 with
      | True -> b2
      | False -> (bool_not b2))
;;
