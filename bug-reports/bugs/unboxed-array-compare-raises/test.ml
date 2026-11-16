let () =
  match compare (Sys.opaque_identity [| #1L; #2L |]) [| #1L; #2L |] with
  | n -> Printf.printf "result %d\n" n
  | exception Invalid_argument m -> Printf.printf "result Invalid_argument %S\n" m
