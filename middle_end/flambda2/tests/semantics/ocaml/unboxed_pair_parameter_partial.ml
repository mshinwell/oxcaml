(* A function whose first parameter is an unboxed pair, given the pair alone
   and a number later; and a function that takes two unboxed pairs, one at a
   time. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] weigh (p : #(int * int)) (c : int) : int =
  let #(a, b) = p in
  (a * 100) + (b * 10) + c

let[@inline never] cross (p : #(int * int)) (q : #(int * int)) : int =
  let #(a, b) = p in
  let #(c, d) = q in
  (a * d) + (b * c)

let with_pair = weigh #(1, 2)

let pair_then_three = with_pair 3

let pair_then_four = with_pair 4

let with_unknown_pair = weigh #(opaque 5, opaque 6)

let unknown_then_seven = with_unknown_pair 7

let with_first = cross #(2, 3)

let crossed = with_first #(4, 5)

let crossed_again = with_first #(opaque 1, 1)
