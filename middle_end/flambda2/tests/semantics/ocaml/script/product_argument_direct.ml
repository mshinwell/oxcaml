(* The unit of product_argument.ml with a direct call where that one has a
   call of unknown arity: from_ocaml.sh makes its text
   (product_argument_direct.says). A direct call has the parameters of its
   code. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] sum #(a, b) c = a + b + c

let result = sum #(opaque 3, 4) 5
