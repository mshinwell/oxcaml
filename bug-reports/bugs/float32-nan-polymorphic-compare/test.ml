external float32_of_float : float -> float32 = "%float32offloat"

let[@inline never] eq x y = x = y

let () =
  let nan = float32_of_float (Sys.opaque_identity Float.nan) in
  Printf.printf "result %b\n" (eq nan nan)
