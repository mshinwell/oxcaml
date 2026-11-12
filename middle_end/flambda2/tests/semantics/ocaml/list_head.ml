(* A list written out and matched at once. Simplify inlines [first_two] and
   resolves the match: no cons cell is read. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] first_two list = match list with x :: y :: _ -> x + y | _ -> 0

let result = first_two [opaque 1; 2; 3]
