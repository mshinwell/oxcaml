(* An option built on both paths of a function that is inlined where its
   condition is not known. The paths then meet in the unit itself, and Simplify
   unboxes the option there: the continuation where they meet is given whether
   the value is an immediate and the field, with [poison] for the field on the
   path of [None]. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] f : bool -> int -> int =
 fun c x ->
  let v = if c then Some (x + 1) else None in
  match v with None -> 0 | Some y -> y + 2

let result = f (opaque true) 3
