let () =
  match Array.make (Sys.opaque_identity (1 lsl 40)) 0 with
  | a -> Printf.printf "result length %d\n" (Array.length a)
  | exception Out_of_memory -> print_endline "result Out_of_memory"
