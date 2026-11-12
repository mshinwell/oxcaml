(* The last element of a list, by a function whose match has the patterns [[x]]
   and [_ :: t]: the front end loads the tail of the list once to test it and
   once more to bind [t], and Simplify loads it once. *)

external opaque : 'a -> 'a = "%opaque"

let rec last l = match l with [] -> 0 | [x] -> x | _ :: t -> last t

let result = last (opaque [5; 6; 7])
