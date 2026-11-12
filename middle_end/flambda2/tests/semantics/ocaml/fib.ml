(* A function that calls itself twice. Simplify leaves the calls. The validator
   is told that the code is recursive and does not inline its calls; when it
   inlined them, in each of its rounds, the term after doubled each round and
   the check did not end. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

let rec fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)

let result = fib 10
