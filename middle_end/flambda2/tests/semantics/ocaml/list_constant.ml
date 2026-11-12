(* A list that one path gives as a constant cell, [[ 5 ]], which is a symbol of
   the unit, and the other as [[]], matched after they meet, in a function that
   is not inlined. Simplify gives the continuation where they meet whether the
   value is an immediate and the head: 5 on the path of the symbol and [poison]
   on the other. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let l = if c then [5] else [] in
  match l with [] -> x | y :: _ -> x + y

let result = f true 3 + f false 4
