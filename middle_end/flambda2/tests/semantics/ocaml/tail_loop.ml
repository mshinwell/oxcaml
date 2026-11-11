(* A tail-recursive loop. Simplify turns the recursive call into a jump to a
   continuation (loopify) and makes the closure of [sum] a symbol. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

let rec sum n acc = if n <= 0 then acc else sum (n - 1) (acc + n)

let result = sum (opaque 10) 0
