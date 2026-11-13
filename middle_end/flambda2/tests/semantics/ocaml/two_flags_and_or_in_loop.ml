(* Two flags kept in references that a loop sets, one to itself and a test and
   the other to itself or a test, and whose conjunction the function returns.
   After Simplify each of the two continuations where the arms meet has its flag
   twice, as a value and as a number. *)

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external ( && ) : bool -> bool -> bool = "%sequand"

external ( || ) : bool -> bool -> bool = "%sequor"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] all_below_and_some_above (n : int) (a : int) (b : int) : bool
    =
  let p = ref true in
  let q = ref false in
  for i = 0 to n do
    p := !p && i < a;
    q := !q || i > b
  done;
  !p && !q

let result = all_below_and_some_above (opaque 9) 20 3
