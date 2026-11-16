let f c x =
  let p = if c then (x, 1) else (2, x) in
  snd p

let () = Printf.printf "result %d\n" (f (Sys.opaque_identity false) 5)
