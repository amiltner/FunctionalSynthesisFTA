let logging = ref false

let log thunk =
  if !logging then
    print_endline (thunk ())
  else
    ()

let path_to_vata = ref "../libvata/build/cli/vata"
