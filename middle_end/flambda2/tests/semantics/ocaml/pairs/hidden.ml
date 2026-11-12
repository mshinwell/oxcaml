(* The first unit of a pair: a module block with a field of which the .cmx says
   what it holds, and one of which it says nothing. *)

external opaque : 'a -> 'a = "%opaque"

let known = 5

let hidden = opaque 7
