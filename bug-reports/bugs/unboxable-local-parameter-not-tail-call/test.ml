let[@inline never] sum (local_ (p : int * int)) = fst p + snd p

let rec loop : (int * int) @ local -> int -> int -> int =
 fun (p [@unboxable]) n acc ->
  if n = 0 then acc else loop p (n - 1) (acc + sum p)

let () = Printf.printf "result %d\n" (loop (stack_ (3, 4)) 10_000_000 0)
