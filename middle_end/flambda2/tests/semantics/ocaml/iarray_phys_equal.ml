(* An immutable array compared with itself by [==]. The model gives the
   comparison of an array with itself no value, as of any two allocated
   values, so the unit is undefined before Simplify and after. *)

external opaque : 'a -> 'a = "%opaque"

external ( == ) : 'a -> 'a -> bool = "%eq"

let table = [: 1; 2; 3 :]

let result = if opaque table == opaque table then 1 else 0
