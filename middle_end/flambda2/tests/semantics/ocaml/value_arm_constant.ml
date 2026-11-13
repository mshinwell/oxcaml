(* The value arm of a [match .. with exception] gives a constant and binds
   nothing; the handler catches everything; the function stays. *)
external raise : exn -> 'a = "%raise"

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] check n = if n < 0 then raise Not_found

let[@inline never] ok n = match check n with () -> 1 | exception _ -> 0

let result = ok (opaque 3) + ok (opaque (-3))
