(* A constant list and a function that reads its head. *)

let primes = [2; 3; 5]

let first_prime () = match primes with [] -> 0 | p :: _ -> p
