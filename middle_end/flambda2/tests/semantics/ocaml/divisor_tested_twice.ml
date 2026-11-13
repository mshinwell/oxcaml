(* A quotient and a remainder by the same divisor. Each division tests that the
   divisor is not zero. Simplify, in the arm where the first test has passed,
   knows the answer of the second, and the second test is gone. *)

external ( / ) : int -> int -> int = "%divint"

external ( mod ) : int -> int -> int = "%modint"

external ( * ) : int -> int -> int = "%mulint"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] digits a b = (a / b * 10) + (a mod b)

let result = digits 17 (opaque 5)
