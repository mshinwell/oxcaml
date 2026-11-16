let[@inline never] positive x strict =
  if 0 < x then x else if strict then raise Not_found else raise Not_found

let () =
  Printf.printf "result %d\n" (positive (Sys.opaque_identity 5) (Sys.opaque_identity true))
