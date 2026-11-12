(* A match on an option of a pair that an inlined function builds on one path
   only. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline] ordered_pair a b = if a < b then Some (a, b) else None

let[@inline never] width a b =
  match ordered_pair a b with Some (low, high) -> high - low | None -> 0

let result = width (opaque 3) (opaque 11) + width (opaque 8) (opaque 2)
