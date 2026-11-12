(* The reversal of a list by a tail-recursive function. *)

external ( - ) : int -> int -> int = "%subint"

let rec rev_onto acc list =
  match list with [] -> acc | x :: rest -> rev_onto (x :: acc) rest

let[@inline] head list = match list with [] -> 0 | x :: _ -> x

let result = head (rev_onto [] [1; 2; 3]) - 1
