let[@inline never] mk (a : int) (b : int) = exclave_ stack_ (a, b)

let[@inline never] g a b c =
  let q = mk a b in
  let x = fst q in
  let finish y =
    let p = Sys.opaque_identity (stack_ (y + 1000, y + 2000)) in
    let u, v = p in
    x + u + v - 3000 - (2 * y)
  in
  if c then exclave_ finish 1 else exclave_ finish 2

let () = Printf.printf "result %d\n" (g 10 20 (Sys.opaque_identity true))
