(* The first component of a pair is read before a call and again after it
   returns, in a function that is inlined. Result: 1. *)

external opaque : 'a -> 'a = "%opaque"

external fst : 'a * 'b -> 'a = "%field0_immut"

let[@inline] both p = if (fst p) 0 then (fst p) 1 else false

let result = if both (opaque ((fun _ -> true), 0)) then 1 else 0
