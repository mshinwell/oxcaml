let[@inline never] apply (g : (int -> int -> int) @ local)
    (_ : (int * int * int * int) @ local) =
  g 10 20

let[@inline never] choose limit =
  let bounds = stack_ (limit, limit + 1) in
  let poly_ pick yes no = let lo, hi = bounds in if lo < hi then yes else no in
  let instance () = pick in
  let chosen = instance () in
  let other = stack_ (limit, limit, limit, limit) in
  Printf.printf "result %d\n" (apply chosen other)

let () = choose 5
