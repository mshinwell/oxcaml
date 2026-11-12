(* The remainder by the constant zero: raises always. *)

external ( mod ) : int -> int -> int = "%modint"

external opaque : 'a -> 'a = "%opaque"

let result = try opaque 7 mod 0 with _ -> -1
