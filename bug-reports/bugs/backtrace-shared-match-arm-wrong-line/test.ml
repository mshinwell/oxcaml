exception E

let[@inline never] f k =
  match k with
  | 0 -> raise E
  | 1 -> raise E
  | _ -> 0

let () =
  Printexc.record_backtrace true;
  try ignore (f (Sys.opaque_identity 1))
  with E ->
    let bt = Printexc.get_raw_backtrace () in
    Printexc.print_raw_backtrace stdout bt;
    match Printexc.backtrace_slots bt with
    | Some s ->
      (match Printexc.Slot.location s.(0) with
       | Some l -> Printf.printf "result line %d\n" l.line_number
       | None -> ())
    | None -> ()
