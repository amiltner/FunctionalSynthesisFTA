open Core

let write_to_file
    ~(fname:string)
    ~(contents:string)
  : unit =
  Out_channel.write_all fname ~data:contents

let read_from_file
    ~(fname:string)
  : string =
  In_channel.read_all fname
