exception E of int

let[@inline never] f a b =
  try
    let q = Sys.opaque_identity (stack_ (a, b)) in
    let x = fst q in
    if b > 0 then raise (E x) else 0
  with E y ->
    let p = Sys.opaque_identity (stack_ (b + 1000, b + 2000)) in
    let u, v = p in
    y + u + v - 3000 - (2 * b)

let () = Printf.printf "result %d\n" (f 10 20)
