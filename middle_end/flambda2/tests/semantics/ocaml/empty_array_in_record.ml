(* The array with no element as a field of a record that is a constant: the
   record is a symbol whose field is the symbol of the empty array. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external string_length : string -> int = "%string_length"

external alength : 'a array -> int = "%array_length"

type basket =
  { owner : string;
    items : int array
  }

let basket = { owner = "nobody"; items = [||] }

let result = string_length basket.owner + alength (opaque basket).items
