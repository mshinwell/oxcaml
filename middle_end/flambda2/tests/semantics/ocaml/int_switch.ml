(* A match on a number with several cases, on an argument that is known once the
   function is inlined. *)

let[@inline] weight n =
  match n with 0 -> 10 | 1 -> 20 | 2 -> 30 | 3 -> 40 | _ -> 50

external ( + ) : int -> int -> int = "%addint"

let result = weight 2 + weight 7
