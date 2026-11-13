(* A pair of GADT values with one index: of the four pairs of constructors the
   type allows two. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( && ) : bool -> bool -> bool = "%sequand"

external opaque : 'a -> 'a = "%opaque"

type _ ty =
  | I : int ty
  | B : bool ty

let[@inline never] same : type a. a ty -> a ty -> a -> a -> int =
 fun t u x y ->
  match t, u with I, I -> x + y | B, B -> if x && y then 1 else 0

let result =
  same I I (opaque 3) 4
  + (same B B (opaque true) true * 10)
  + (same B (opaque B) false true * 100)
