(* An immutable array of constants, read at an index that is not known
   and measured. Simplify makes the array a symbol bound to a static
   array, which the validation does not follow: the two runs are the
   same, and the unit is not validated. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external get : 'a iarray -> int -> 'a = "%array_unsafe_get"

external length : 'a iarray -> int = "%array_length"

let primes = [: 2; 3; 5; 7; 11 :]

let result = get primes (opaque 3) + length primes
