(* Functions of two to six parameters, each given all its arguments but the
   last; what is left is bound to a name and given the last argument twice. None
   of the functions is inlined. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] two a b = (a * 10) + b

let[@inline never] three a b c = (((a * 10) + b) * 10) + c

let[@inline never] four a b c d = (((((a * 10) + b) * 10) + c) * 10) + d

let[@inline never] five a b c d e =
  (((((((a * 10) + b) * 10) + c) * 10) + d) * 10) + e

let[@inline never] six a b c d e f =
  (((((((((a * 10) + b) * 10) + c) * 10) + d) * 10) + e) * 10) + f

let last = opaque 9

let two_but_last = two 1

let of_two = two_but_last last + two_but_last 0

let three_but_last = three 1 2

let of_three = three_but_last last + three_but_last 0

let four_but_last = four 1 2 3

let of_four = four_but_last last + four_but_last 0

let five_but_last = five 1 2 3 4

let of_five = five_but_last last + five_but_last 0

let six_but_last = six 1 2 3 4 5

let of_six = six_but_last last + six_but_last 0
