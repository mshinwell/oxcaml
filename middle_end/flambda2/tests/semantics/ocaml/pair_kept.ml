(* A pair that is read after two paths meet and is also returned, so that it
   stays a parameter beside its fields. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

let[@inline never] sum : bool -> int * int -> int * (int * int) =
 fun c pair ->
  let p = if c then 1, 2 else pair in
  fst p + snd p, p

let result = fst (sum true (3, 4)) + fst (sum false (5, 6))
