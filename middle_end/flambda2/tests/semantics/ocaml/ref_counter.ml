(* A counter in a [ref]. The [ref] goes through [%opaque], so nothing is known
   of it and it stays a block: one allocation, two increments through a function
   that is not inlined, one read. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] tick (counter : int ref) : unit = counter := !counter + 1

let counter : int ref = opaque (ref 0)

let () =
  tick counter;
  tick counter

let result = !counter
