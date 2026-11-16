let rec loop n acc =
  if (n, acc) = (0, 0) then acc
  else if n = 0 then acc
  else Fun.id (loop (n - 1) (acc + 1))

let () = Printf.printf "result %d\n" (loop 10_000_000 0)
