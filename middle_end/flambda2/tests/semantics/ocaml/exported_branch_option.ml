(* An option chosen by a test when the module runs, and a function that reads it
   with a default. *)

external opaque : 'a -> 'a = "%opaque"

let setting = if opaque true then Some 5 else None

let get () = match setting with Some n -> n | None -> 0
