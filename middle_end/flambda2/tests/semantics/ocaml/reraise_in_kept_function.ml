(* A function that stays, with a handler that raises again what it caught unless
   a test says otherwise; nothing in the unit names an exception. *)
external raise : exn -> 'a = "%raise"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] guarded f x =
  try f x + 1 with e -> if opaque true then raise e else 0

let result =
  guarded (fun x -> x + x) (opaque 2) + guarded (fun x -> x + 1) (opaque 3)
