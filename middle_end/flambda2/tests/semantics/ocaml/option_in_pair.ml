(* A pair whose first component is an option, made on the two arms of a test:
   the second component is loaded in each arm of the match on the first. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] total c x y =
  let p = if c then Some x, y else None, y + 1 in
  match fst p with Some v -> v + snd p | None -> snd p

let result = total (opaque true) 5 30 + total (opaque false) 5 30
