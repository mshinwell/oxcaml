(* An immutable array made of the arguments of a function that is not
   inlined, read and measured where the function is called. Simplify
   leaves the array to be made where it is: the two terms make it
   alike. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external get : 'a iarray -> int -> 'a = "%array_unsafe_get"

external length : 'a iarray -> int = "%array_length"

let[@inline never] three a b = [: a; b; a + b :]

let result =
  let values = three (opaque 2) (opaque 5) in
  get values 2 + length values
