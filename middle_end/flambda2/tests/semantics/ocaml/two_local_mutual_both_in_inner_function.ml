(* An inner function that is never inlined, with two local functions that call
   each other, each given to an inlined function. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

let make n =
  let[@inline never] later y =
    let rec down k = if k = 0 then n else up (k - 1)
    and up k = if k = 0 then y else down (k - 1) in
    apply down 2 + apply up 1
  in
  later

let result = (make (opaque 3)) 4
