(* Calls of a function of another unit that is one of a set of two: one in a
   function, one at toplevel. *)

let even_or_odd n = if Parity.even n then 0 else 1

let four_is_even = Parity.even 4
