(* A while loop that stops when a flag is set or one of two bounds is passed,
   written with a disjunction under a negation. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( > ) : int -> int -> bool = "%greaterthan"

external not : bool -> bool = "%boolnot"

external ( || ) : bool -> bool -> bool = "%sequor"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] steps_until (n : int) (m : int) : int =
  let stop = ref false in
  let i = ref 0 in
  while not (!stop || !i > n || !i > m) do
    i := !i + 1;
    if !i * !i > 20 then stop := true
  done;
  !i

let result = steps_until (opaque 9) 7
