(* A function with an optional argument given where a function without one is
   expected: the compiler makes the function that omits it. *)
external ( + ) : int -> int -> int = "%addint"

let[@inline never] twice (g : int -> int) x = g (g x)

let bump ?(by = 1) x = x + by

let[@inline never] bump_kept ?(by = 100) x = x + by

let erased = twice bump 5

let erased_kept = twice bump_kept 5

let given_first = twice (bump ~by:10) 5

let given_first_kept = twice (bump_kept ~by:20) 5
