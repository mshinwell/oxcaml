type r = { x : float; y : float }

let r1 = { x = 1.0; y = 2.0 }
let r2 = { x = 1.0; y = 2.0 }
let p1 = (1, 2)
let p2 = (1, 2)

let () = Printf.printf "result %b %b\n" (p1 == p2) (r1 == r2)
