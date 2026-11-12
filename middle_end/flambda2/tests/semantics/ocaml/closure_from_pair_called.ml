(* Two local closures put in a pair, taken out and called. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let run n =
  let add x = x + n in
  let scale x = x * n in
  let f, g = add, scale in
  f 1 + g 2 + f 3 + g 4

let result = run (opaque 10)
