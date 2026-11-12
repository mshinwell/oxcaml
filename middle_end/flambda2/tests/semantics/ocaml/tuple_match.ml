(* A match on a pair of integers, at four pairs of constants. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline] classify a b =
  match a, b with 0, 0 -> 0 | 0, _ -> 1 | _, 0 -> 2 | _, _ -> 3

let result = classify 0 0 + classify 0 5 + classify 5 0 + classify 5 5
