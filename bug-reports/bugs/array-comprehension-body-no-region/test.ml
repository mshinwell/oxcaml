let[@inline never] use (p : int * int @ local) = fst p + snd p

let[@inline never] f n = [| use (stack_ (i, i + 1)) for i = 1 to n |]

let () = Printf.printf "result %d\n" (Array.length (f 4_000_000))
