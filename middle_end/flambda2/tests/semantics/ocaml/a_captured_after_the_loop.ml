(* A ref updated in a loop with a raise and a handler that writes it, captured
   by a local function only after the try; it is written once more and read by
   that function. gives: stopped = 11 | finished = 16 | at_once = 2 | empty =
   1 *)

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

let run (n : int) (k : int) =
  let a = ref 0 in
  (try
     for i = 1 to n do
       a := !a + i;
       if i = k then raise (Failure "stop");
       ()
     done;
     ()
   with Failure _ ->
     a := !a + (0 * 100);
     ());
  let get () = !a in
  a := !a + 1;
  let v = get () in
  v

let stopped : int = run (opaque 6) (opaque 4)

let finished : int = run 5 9

let at_once : int = run (opaque 3) 1

let empty : int = run 0 0
