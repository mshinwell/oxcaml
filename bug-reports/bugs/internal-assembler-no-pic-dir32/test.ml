let[@inline never] f x = try x () with Not_found -> 0

let () = Printf.printf "result %d\n" (f (fun () -> raise Not_found))
