let[@inline never] f (a : float array) i x = x *. Array.unsafe_get a i

let () = Printf.printf "result %g\n" (f [| 2. |] 0 3.)
