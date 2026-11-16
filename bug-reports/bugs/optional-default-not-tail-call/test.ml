let one = Sys.opaque_identity 1

let rec loop ?(step = if (one, 2) = (1, 2) then 1 else 0) n acc =
  if n = 0 then acc else loop (n - 1) (acc + step)

let () = Printf.printf "result %d\n" (loop 10_000_000 0)
