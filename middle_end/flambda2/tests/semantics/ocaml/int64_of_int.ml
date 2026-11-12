(* Conversions between [int] and [int64] around an addition. Simplify inlines
   [add_as_int64]; no box is left. *)

external opaque : 'a -> 'a = "%opaque"

external of_int : int -> int64 = "%int64_of_int"

external to_int : int64 -> int = "%int64_to_int"

external add : int64 -> int64 -> int64 = "%int64_add"

let[@inline] add_as_int64 a b = to_int (add (of_int a) (of_int b))

let result = add_as_int64 (opaque 40) 2
