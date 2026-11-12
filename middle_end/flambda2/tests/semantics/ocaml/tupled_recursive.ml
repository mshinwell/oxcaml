(* A recursive function whose parameter is a pair pattern: the count and the sum
   so far. Each call, the one in the function too, is written with a pair;
   Simplify makes each a direct call that gives the code the components. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

let rec sum (n, acc) = if n <= 0 then acc else sum (n - 1, acc + n)

let result = sum (opaque 10, 0)
