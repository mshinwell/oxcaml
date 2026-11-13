(* A ref that holds a constant on one path and another on the other, then a try
   in which it is written after a possible raise, and whose handler multiplies
   it. gives: both = 50 | first = 6 | second = 0 | neither = 1 | both_unknown =
   50 *)

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

let run (c : bool) (d : bool) =
  let r = ref 0 in
  if c
  then (
    r := 5;
    ());
  (try
     if d then raise Division_by_zero;
     r := !r + 1;
     ()
   with Division_by_zero ->
     r := !r * 10;
     ());
  !r

let both : int = run true true

let first : int = run (opaque true) false

let second : int = run false (opaque true)

let neither : int = run (opaque false) (opaque false)

let both_unknown : int = run (opaque true) (opaque true)
