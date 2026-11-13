(* A match on a variant, and in the arm of one constructor a second match on the
   same value, inlined. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type amount =
  | Free
  | Fixed of int
  | Percent of int

let[@inline] value_of a base =
  match a with Free -> 0 | Fixed n -> n | Percent p -> base * p

let[@inline never] price a base =
  match a with Fixed _ -> value_of a base + 1 | Percent p -> p | Free -> 0

let result =
  price (opaque (Fixed 4)) (opaque 10)
  + price (opaque (Percent 3)) (opaque 10)
  + price (opaque Free) (opaque 10)
