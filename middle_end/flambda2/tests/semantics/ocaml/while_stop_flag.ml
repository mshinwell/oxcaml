(* A loop that a flag stops: the condition of the loop reads the flag first, and
   the body sets it under a test. *)

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

let[@inline never] sum_until (n : int) (limit : int) : int =
  let sum = ref 0 in
  let stop = ref false in
  let i = ref 0 in
  while if !stop then false else !i < n do
    sum := !sum + !i;
    if limit < !sum then stop := true;
    i := !i + 1
  done;
  !sum

let result = sum_until (opaque 9) 7
