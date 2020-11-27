let logging = ref false

let log thunk =
  if !logging then
    print_endline (thunk ())
  else
    ()

let path_to_vata = ref "../../libvata/build/cli/vata"

let isect_time = ref 0.0

let time t f =
  let init = Sys.time () in
  let ans = f () in
  t := (!t +. (Sys.time() -. init));
  ans
