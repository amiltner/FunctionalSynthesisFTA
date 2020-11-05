let logging = ref false

let log thunk =
  if !logging then
    print_endline (thunk ())
  else
    ()
