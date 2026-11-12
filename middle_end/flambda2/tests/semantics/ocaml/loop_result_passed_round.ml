(* A tail-recursive function that passes to itself its counter or what a loop
   inside it leaves, where the loop may leave the accumulator of the
   function. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let rec settle n acc =
  if n <= 0
  then acc
  else
    settle (n - 1)
      (if acc < n
       then n
       else
         let i = ref 0 in
         let last = ref 0 in
         while !i < opaque 2 do
           last := acc;
           i := !i + 1
         done;
         !last)

let result = settle (opaque 3) (opaque 6)
