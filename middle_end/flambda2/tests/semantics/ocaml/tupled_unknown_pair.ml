(* A function whose parameter is a pair pattern and that is never inlined, given
   a pair that is not known. Simplify knows the function: it reads the two
   fields of the pair and makes the call direct. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] add (a, b) = a + b

let result = add (opaque (1, 2))
