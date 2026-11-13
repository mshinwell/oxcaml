(* A function that calls itself last; each turn defines two local functions that
   call each other and gives each to an inlined function. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

let rec walk n acc =
  if n = 0
  then acc
  else
    let rec down k = if k = 0 then n else up (k - 1)
    and up k = if k = 0 then acc else down (k - 1) in
    walk (n - 1) (apply down 2 + apply up 1)

let result = walk (opaque 3) 0
