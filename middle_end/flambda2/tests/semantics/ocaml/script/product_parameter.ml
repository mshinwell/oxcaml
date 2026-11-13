(* A call of unknown arity, in a unit that has a function of an unboxed pair:
   from_ocaml.sh refuses it (product_parameter.says). The text writes the
   parameters of that function as two, and nothing in it says that the call
   of unknown arity does not reach it. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] sum #(a, b) = a + b

let[@inline never] g (x : int) = x + 1

let result = sum #(opaque 3, 4), (opaque g) 1
