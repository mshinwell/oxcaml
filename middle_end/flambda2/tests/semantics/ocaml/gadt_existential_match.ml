(* A packed pair of a witness and a value, opened and matched: both arms are
   live. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type _ t =
  | Int : int t
  | Bool : bool t

type packed = Pack : 'a t * 'a -> packed

let unpack (p : packed) : int =
  match p with Pack (Int, x) -> x | Pack (Bool, b) -> if b then 1 else 0

let result =
  unpack (opaque (Pack (Int, 7))) + unpack (opaque (Pack (Bool, true)))
