(* A function that is kept, with a loop that makes, at each round, a function
   that captures nothing and gives it to something that is not known. Simplify
   makes that function a symbol, bound beside the code of the first: the loop is
   the handler of a recursive continuation in that code. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] sum_of_successors n =
  let s = ref 0 in
  for i = 1 to n do
    s := !s + (opaque (fun x -> x + 1)) i
  done;
  !s

let result = sum_of_successors (opaque 3)
