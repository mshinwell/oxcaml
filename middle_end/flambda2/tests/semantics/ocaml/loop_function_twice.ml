(* A function with a loop that makes, at each round, a function that captures
   nothing, inlined twice when the module runs. The two loops make the same
   closure: Simplify has one symbol for both. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline] sum_of_successors n =
  let s = ref 0 in
  for i = 1 to n do
    s := !s + (opaque (fun x -> x + 1)) i
  done;
  !s

let result = sum_of_successors (opaque 2) + sum_of_successors (opaque 3)
