(* A closure over a pair that reads one field twice. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] doubler pair = fun x -> x + fst pair + fst pair

let result = (doubler (opaque 3, 0)) 4
