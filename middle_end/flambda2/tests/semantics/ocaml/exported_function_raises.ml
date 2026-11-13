(* A unit that exports a function which raises, and a function which catches
   what the first raises. *)
external raise : exn -> 'a = "%raise"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

let pred n = if n < 1 then raise Not_found else n - 1

let pred_or_zero n = try pred n with Not_found -> 0

let result = pred_or_zero 0
