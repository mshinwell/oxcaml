(* An exported function whose body is a local loop, written as a tail-recursive
   function that is to be inlined. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let sum_to n =
  let[@inline] rec go total i =
    if i = 0 then total else go (total + i) (i - 1)
  in
  go 0 n

let result = sum_to (opaque 4)
