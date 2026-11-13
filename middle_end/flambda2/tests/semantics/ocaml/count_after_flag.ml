(* A count of the turns of a loop after a flag is set: the flag is tested at
   every turn, and set under a test where it is not. The arm that does not set
   it passes it on, and it is known to be clear there, so the two arms of the
   inner test give their own numbers: Simplify passes the result of the test. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] turns_after (n : int) (limit : int) : int =
  let seen = ref false in
  let after = ref 0 in
  for i = 0 to n do
    if !seen then after := !after + 1 else if i * 3 > limit then seen := true
  done;
  if !seen then !after else -1

let result = turns_after (opaque 9) 7
