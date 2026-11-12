(* A pair that is built on one path and given on the other, and read after the
   two paths meet. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

let[@inline never] sum : bool -> int * int -> int =
 fun c pair ->
  let p = if c then 1, 2 else pair in
  fst p + snd p

let result = sum true (3, 4) + sum false (5, 6)
