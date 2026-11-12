(* A pair of strings swapped twice by a function that is inlined, and its first
   field read by another. The function that is never inlined, which the unit
   exports, holds the two functions in value slots of its closure and calls them
   through the slots. Simplify inlines the three calls and removes the slots and
   the closures of the two functions, which the unit does not export: the term
   after does not make them. The pair is of strings so that no kind of the unit
   may be null. *)

external fst : 'a * 'b -> 'a = "%field0_immut"

external opaque : 'a -> 'a = "%opaque"

let[@inline] swap (a, b) : string * string = b, a

let[@inline] first pair = fst pair

let[@inline never] back pair = first (swap (swap pair))

let result = back (opaque "one", "two")
