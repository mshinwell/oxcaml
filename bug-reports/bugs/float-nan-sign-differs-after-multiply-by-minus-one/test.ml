let[@inline never] times_minus_one x = x *. -1.

let () =
  Printf.printf "result %b\n"
    (Float.sign_bit (times_minus_one (Sys.opaque_identity Float.nan)))
