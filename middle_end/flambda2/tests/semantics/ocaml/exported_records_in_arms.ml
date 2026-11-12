(* A record chosen by a test when the module runs: each arm makes a record of a
   function and a number. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

type t =
  { apply : int -> int;
    base : int
  }

let r =
  if opaque true
  then { apply = (fun x -> x + 1); base = 1 }
  else { apply = (fun x -> x + 2); base = 2 }
