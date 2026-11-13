(* Composition of functions as a combinator: two functions, three by nesting on
   either side, a composition kept and applied to several arguments, and a
   composition of partial applications. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let compose f g x = f (g x)

let[@inline never] add a b = a + b

let[@inline never] scale a b = a * b

let increment x = x + 1

let double x = x * 2

let square x = x * x

let x = opaque 3

let two = compose increment double x

let three_left = compose (compose increment double) square x

let three_right = compose increment (compose double square) x

let kept = compose square increment

let kept_applied = kept 1 + kept 2 + kept x

let of_partials = compose (add 10) (scale 4) x
