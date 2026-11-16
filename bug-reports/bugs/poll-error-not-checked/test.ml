let[@poll error] f x = (x, x + 1)

let () =
  let a, b = f (Sys.opaque_identity 3) in
  Printf.printf "result %d\n" (a + b)
