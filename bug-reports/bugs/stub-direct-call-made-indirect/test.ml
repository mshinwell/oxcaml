let[@zero_alloc] f ?(step = 1) n = n + step

let () = Printf.printf "result %d\n" (f 41)
