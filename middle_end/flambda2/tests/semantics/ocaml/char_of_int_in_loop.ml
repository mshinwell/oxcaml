(* A loop over the numbers 0 to 9 that makes the digit character of each and
   compares it with a character of a constant string. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

external unsafe_chr : int -> char = "%identity"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

external ( = ) : 'a -> 'a -> bool = "%equal"

let rec count i acc =
  if i < 10
  then
    let c = unsafe_chr (i + code '0') in
    count (i + 1) (if c = unsafe_get "0123456789" i then acc + 1 else acc)
  else acc

let result = count (opaque 0) 0
