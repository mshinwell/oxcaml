(* An identity of arithmetic: Simplify makes [x + 0] into [x]. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let result = opaque 3 + 0
