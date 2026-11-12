(* Two results that Simplify computes to the same boxed constant: one symbol is
   bound to it, and both fields of the module are that symbol. *)

external add : int64 -> int64 -> int64 = "%int64_add"

let one_plus_two = add 1L 2L

let two_plus_one = add 2L 1L
