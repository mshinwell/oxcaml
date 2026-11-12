(* A [while] loop over two [ref]s that do not leave the function: the front end
   makes them variables, and no block is made. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( / ) : int -> int -> int = "%divint"

external ( land ) : int -> int -> int = "%andint"

external ( = ) : int -> int -> bool = "%equal"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

external incr : int ref -> unit = "%incr"

let collatz_steps start =
  let n = ref start in
  let steps = ref 0 in
  while !n > 1 do
    if !n land 1 = 0 then n := !n / 2 else n := (3 * !n) + 1;
    incr steps
  done;
  !steps

let result = collatz_steps (opaque 27)
