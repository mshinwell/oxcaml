(* Two partial applications of one inlined function kept in a pair and
   applied. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] combine a b c = (a * 100) + (b * 10) + c

let[@inline never] body x =
  let fs = combine x 1, combine 1 x in
  let f, g = fs in
  f 5 + g 6

let result = body (opaque 2) + body 9
