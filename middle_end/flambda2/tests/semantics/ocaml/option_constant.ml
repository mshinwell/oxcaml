(* An option that one path gives as a constant block, [Some 8], which is a
   symbol of the unit, and the other as [None], matched after they meet, in a
   function that is not inlined. Simplify gives the continuation where they meet
   whether the value is an immediate and the field: 8 on the path of the symbol
   and [poison] on the other. The validation knows the block in the code of the
   function, as the symbol is bound above the code. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then Some 8 else None in
  match v with None -> x | Some y -> x + y

let result = f true 3 + f false 4
