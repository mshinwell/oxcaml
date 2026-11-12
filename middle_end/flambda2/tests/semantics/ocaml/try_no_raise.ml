(* A handler around an expression that cannot raise. *)

external opaque : 'a -> 'a = "%opaque"

let result = try opaque 1 with _ -> 2
