exception Error

let[@inline never] fail () = raise Error

let[@inline never] check x = if x < 0 then 1 + fail () else x

let () =
  Printexc.record_backtrace true;
  try ignore (check (Sys.opaque_identity (-1)))
  with Error ->
    let bt = Printexc.get_raw_backtrace () in
    Printexc.print_raw_backtrace stdout bt;
    Printf.printf "result %d frames\n" (Printexc.raw_backtrace_length bt)
