(* A ref that does not escape, updated in place in a for loop; a raise_notrace
   in the body; the try is around the loop and its handler gives the value.
   gives: stopped = 6026 | finished = 114 | at_once = 6001 | empty = 0 *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external ( / ) : int -> int -> int = "%divint"

external ( = ) : int -> int -> bool = "%equal"

external ( <> ) : int -> int -> bool = "%notequal"

external ( < ) : int -> int -> bool = "%lessthan"

external ( <= ) : int -> int -> bool = "%lessequal"

external ( > ) : int -> int -> bool = "%greaterthan"

external ( >= ) : int -> int -> bool = "%greaterequal"

external ( && ) : bool -> bool -> bool = "%sequand"

external ( || ) : bool -> bool -> bool = "%sequor"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

external incr : int ref -> unit = "%incr"

external raise : exn -> 'a = "%raise"

external raise_notrace : exn -> 'a = "%raise_notrace"

external opaque : 'a -> 'a = "%opaque"

module Array = struct
  external length : 'a array -> int = "%array_length"

  external get : 'a array -> int -> 'a = "%array_safe_get"

  external set : 'a array -> int -> 'a -> unit = "%array_safe_set"
end

let[@inline never] [@local never] run (n : int) (k : int) =
  let a = ref 0 in
  let r =
    try
      for i = 1 to n do
        a := !a + i;
        if i = k then raise_notrace (Failure "stop");
        a := !a * 2;
        ()
      done;
      !a
    with Failure _ ->
      a := !a + (1000 + 0);
      !a + 5000
  in
  r

let stopped : int = run (opaque 6) (opaque 4)

let finished : int = run 5 9

let at_once : int = run (opaque 3) 1

let empty : int = run 0 0
