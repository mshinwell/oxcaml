(* A recursive function of one argument that returns a function, applied to two
   arguments at once, where the module runs and in the function that it returns.
   A call of two arguments is a call of the function and then a call of what it
   returns. The closure returned holds the recursive function in a value slot;
   Simplify makes its code call the symbol of the recursive function. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let rec times n = if n = 0 then fun b -> b else fun b -> times (n - 1) (b + b)

let result = times (opaque 3) 1
