open Core

let write_to_file
    ~(fname:string)
    ~(contents:string)
  : unit =
  let fd = Unix.openfile ~mode:[O_WRONLY;O_CREAT;O_TRUNC] fname in
  let pos = 0 in
  let len = String.length contents in
  let _ = Unix.single_write_substring ~pos ~len fd ~buf:contents in
  Unix.close fd

let read_from_file
    ~(fname:string)
  : string =
  In_channel.read_all fname
