(* A character is its code. Simplify inlines [digit_value]: one subtraction is
   left. *)

external code : char -> int = "%identity"

external ( - ) : int -> int -> int = "%subint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] digit_value c = code c - code '0'

let result = digit_value (opaque '7')
