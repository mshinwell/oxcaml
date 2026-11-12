(* A pair that is computed on both paths and read after they meet. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

let[@inline never] sum : bool -> int -> int =
 fun c x ->
  let p = if c then x + 1, 1 else 2, x + 2 in
  fst p + snd p

let result = sum true 3 + sum false 4
