(* A search with a flag: the loop goes on while the flag is not set and there is
   more to look at, and the flag is tested again after the loop. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external not : bool -> bool = "%boolnot"

external ( && ) : bool -> bool -> bool = "%sequand"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] first_above (n : int) (limit : int) : int =
  let found = ref false in
  let i = ref 0 in
  while (not !found) && !i < n do
    if !i * 3 > limit then found := true else i := !i + 1
  done;
  if !found then !i else -1

let result = first_above (opaque 9) 7
