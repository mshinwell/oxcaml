(* The function applied after a test is, on each side, a partial application: of
   the same function with different arguments, of two functions with the same
   number of arguments left, and of functions of which one is complete but for
   one argument and the other has taken none. *)
external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] add a b = a + b

let[@inline never] sub a b = a - b

let[@inline never] three a b c = (a * 100) + (b * 10) + c

let negate x = 0 - x

let[@inline never] same_function (c : bool) : int =
  let f = if c then add 1 else add 2 in
  f 10

let[@inline never] two_functions (c : bool) : int =
  let f = if c then add 1 else sub 1 in
  f 10

let[@inline never] different_depths (c : bool) : int =
  let f = if c then three 1 2 else negate in
  f 3

let same_true = same_function (opaque true)

let same_false = same_function (opaque false)

let two_true = two_functions (opaque true)

let two_false = two_functions (opaque false)

let depths_true = different_depths (opaque true)

let depths_false = different_depths (opaque false)
