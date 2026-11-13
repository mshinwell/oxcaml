(* A while loop whose condition tests a flag and then, in each arm, updates a
   count of its own and tests it. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] two_phases (n : int) : int =
  let found = ref false in
  let i = ref 0 in
  let s = ref 0 in
  while
    if !found
    then (
      s := !s + 1;
      !s < 3)
    else (
      i := !i + 1;
      !i < n)
  do
    if !i * !i > 20 then found := true
  done;
  !s + !i

let result = two_phases (opaque 9)
