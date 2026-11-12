(* A match on constant constructors is a switch. Simplify inlines [code] twice
   and resolves both. *)

external ( + ) : int -> int -> int = "%addint"

type colour =
  | Red
  | Green
  | Blue

let[@inline] code colour = match colour with Red -> 1 | Green -> 2 | Blue -> 4

let result = code Red + code Blue
