(* The function that is given too many arguments is not known where it is
   applied: it is chosen by a test, or it comes as an argument of a function
   that is kept. *)
external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let adder x =
  let x = x * 10 in
  fun y -> x + y

let subtracter x =
  let x = x * 10 in
  fun y -> x - y

let[@inline never] apply_both (f : int -> int -> int) a b = f a b

let chosen_true = (if opaque true then adder else subtracter) 4 2

let chosen_false = (if opaque false then adder else subtracter) 4 2

let through_argument = apply_both adder 5 1

let through_argument_other = apply_both subtracter 5 1
