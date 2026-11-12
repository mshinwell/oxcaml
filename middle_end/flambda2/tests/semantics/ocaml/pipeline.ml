(* [|>], which the front end turns into applications. *)

external ( |> ) : 'a -> ('a -> 'b) -> 'b = "%revapply"

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] increment x = x + 1

let[@inline] double x = x * 2

let result = opaque 5 |> increment |> double |> increment
