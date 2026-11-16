let ( let* ) x f = f x

let rec loop n acc =
  if n = 0 then acc
  else
    let* a = if (n, acc) = (0, 0) then 0 else acc + 1 in
    loop (n - 1) a

let () = Printf.printf "result %d\n" (loop 10_000_000 0)
