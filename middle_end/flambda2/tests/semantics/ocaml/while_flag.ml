(* A [while] loop that a boolean reference stops: Simplify untags the boolean
   that the loop passes round. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external ( && ) : bool -> bool -> bool = "%sequand"

external not : bool -> bool = "%boolnot"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 7 in
  let found = ref false in
  let i = ref 0 in
  while (not !found) && !i < n do
    if !i * !i > n then found := true else i := !i + 1
  done;
  !i
