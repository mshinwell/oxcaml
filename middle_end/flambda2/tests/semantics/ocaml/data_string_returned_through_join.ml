(* A string chosen by a test and returned, and a field of a record chosen the
   same way. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

type entry =
  { key : string;
    weight : int
  }

let choose c a b = if c then a else b

let result =
  length (choose (opaque true) "left" "right!")
  + length
      (choose (opaque false) { key = "a"; weight = 1 }
         { key = "bcd"; weight = 2 })
        .key
