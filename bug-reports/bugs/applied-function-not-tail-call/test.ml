let rec loop n acc =
  if n = 0 then acc
  else
    let k = if (n, acc) = (0, -1) then 1 else 0 in
    acc + 1 + k |> fun a -> loop (n - 1) a

let () = Printf.printf "result %d\n" (loop 10_000_000 0)
