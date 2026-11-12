(* A closure made by an inlined function, over an argument that is a field of a
   pair. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external opaque : 'a -> 'a = "%opaque"

let[@inline] adder n = fun x -> x + n

let add_first pair = adder (fst pair)

let result = (add_first (opaque 3, 0)) 4
