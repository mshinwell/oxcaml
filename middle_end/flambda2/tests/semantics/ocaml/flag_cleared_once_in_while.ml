(* A flag that a while loop clears once: the loop tests it at every turn, and
   where it is clear nothing more is done but the count. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] first_square_above (n : int) (limit : int) : int =
  let ok = ref true in
  let bad = ref 0 in
  let i = ref 0 in
  while !i < n do
    if !ok
    then
      if !i * !i > limit
      then (
        ok := false;
        bad := !i);
    i := !i + 1
  done;
  if !ok then -1 else !bad

let result = first_square_above (opaque 9) 7
