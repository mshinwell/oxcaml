let[@inline never] first () : unit = raise Exit

let[@inline never] second () : unit = raise Exit

let () =
  Printexc.record_backtrace true;
  (try first () with Exit -> ());
  try second ()
  with Exit ->
    let bt = Printexc.get_raw_backtrace () in
    Printexc.print_raw_backtrace stdout bt;
    Printf.printf "result %d frames\n" (Printexc.raw_backtrace_length bt)
