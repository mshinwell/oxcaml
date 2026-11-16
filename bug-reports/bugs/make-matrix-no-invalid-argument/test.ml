let () =
  match Array.make_matrix 0 (Sys.opaque_identity max_int) 0 with
  | m -> Printf.printf "result %d rows\n" (Array.length m)
  | exception Invalid_argument _ -> print_endline "result Invalid_argument"
