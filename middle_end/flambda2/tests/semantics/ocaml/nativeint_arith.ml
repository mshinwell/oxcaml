(* Arithmetic on boxed native integers. [x] is used twice: the front end unboxes
   it twice, and Simplify once. *)

external opaque : 'a -> 'a = "%opaque"

external add : nativeint -> nativeint -> nativeint = "%nativeint_add"

external sub : nativeint -> nativeint -> nativeint = "%nativeint_sub"

external mul : nativeint -> nativeint -> nativeint = "%nativeint_mul"

let[@inline] f x y = sub (mul x y) (add x y)

let result = f (opaque 6n) 7n
