(* A pair that each path gives as a constant block, both symbols of the unit,
   read after they meet, in a function that is not inlined. Simplify gives the
   continuation where they meet the two fields. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let p = if c then 1, 2 else 3, 4 in
  fst p + snd p + x

let result = f true 3 + f false 4
