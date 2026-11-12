(* A pair whose two fields are the same value on each path. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] spread option default =
  let pair = match option with Some v -> v, v | None -> default, default in
  fst pair - snd pair

let result = spread (opaque (Some 3)) 4 + spread (opaque None) 5
