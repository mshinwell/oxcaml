(* [fst] and [snd] as the standard library declares them. Simplify inlines [sum]
   and reads the two fields of the pair, which is then not built. *)

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] sum pair = fst pair + snd pair

let result = sum (opaque 1, 2)
