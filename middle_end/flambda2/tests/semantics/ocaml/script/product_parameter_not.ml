(* The unit of product_parameter.ml with a function of two integers where that
   one has a function of an unboxed pair: from_ocaml.sh makes its text
   (product_parameter_not.says). *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] sum a b = a + b

let[@inline never] g (x : int) = x + 1

let result = sum (opaque 3) 4, (opaque g) 1
