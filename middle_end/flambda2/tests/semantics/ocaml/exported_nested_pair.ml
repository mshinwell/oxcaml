(* A constant pair of pairs, and an exported function that reads a field of a
   field. *)

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

let table = (1, 2), (3, 4)

let get () = fst (snd table)
