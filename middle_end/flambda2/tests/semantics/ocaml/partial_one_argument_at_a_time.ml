(* A function of six parameters given its arguments one at a time, each partial
   application bound to a name, and two of them used twice. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] six a b c d e f =
  (((((((((a * 10) + b) * 10) + c) * 10) + d) * 10) + e) * 10) + f

let p1 = six (opaque 1)

let p2 = p1 2

let p3 = p2 3

let p4 = p3 4

let p5 = p4 5

let whole = p5 6

let other_end = p5 7

let from_the_middle = p3 0 0 0

let from_the_start = p1 9 9 9 9 9
