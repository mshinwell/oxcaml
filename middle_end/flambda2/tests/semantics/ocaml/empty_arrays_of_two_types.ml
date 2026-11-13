(* Two arrays with no element, of two types: the front end makes one static
   constant of the two. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external alength : 'a array -> int = "%array_length"

let numbers : int array = [||]

let words : string array = [||]

let result = alength (opaque numbers) + alength (opaque words) + 3
