let[@unboxable] rec loop n acc =
  if n = 0 then acc else loop (n - 1) (acc +. 1.)

let () = Printf.printf "result %.0f\n" (loop 10_000_000 0.)
