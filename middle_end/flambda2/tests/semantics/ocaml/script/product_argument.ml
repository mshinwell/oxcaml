(* A call of unknown arity that gives an unboxed pair, which from_ocaml.sh
   refuses (product_argument.says): the text does not say that the two
   arguments of that call are one. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] sum #(a, b) c = a + b + c

let result = (opaque sum) #(3, 4) 5
