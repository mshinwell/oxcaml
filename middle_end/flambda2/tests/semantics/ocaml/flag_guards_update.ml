(* A sum that a flag freezes: the loop adds to the sum while the flag is clear,
   and sets the flag when the sum passes a limit. *)

external ( + ) : int -> int -> int = "%addint"

external ( > ) : int -> int -> bool = "%greaterthan"

external not : bool -> bool = "%boolnot"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] sum_until_above (n : int) (limit : int) : int =
  let frozen = ref false in
  let sum = ref 0 in
  for i = 0 to n do
    if not !frozen
    then (
      sum := !sum + i;
      if !sum > limit then frozen := true)
  done;
  !sum

let result = sum_until_above (opaque 9) 7
