(* The length of a list by a tail-recursive function. Simplify makes the tail
   call a jump and the closure a symbol. *)

external ( + ) : int -> int -> int = "%addint"

let rec length_from acc list =
  match list with [] -> acc | _ :: rest -> length_from (acc + 1) rest

let result = length_from 0 [10; 20; 30; 40]
