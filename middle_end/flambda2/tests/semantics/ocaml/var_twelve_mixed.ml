(* Eight constant constructors and four with arguments, in groups by
   or-patterns. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type token =
  | Lparen
  | Rparen
  | Plus
  | Minus
  | Star
  | Slash
  | Eof
  | Dot
  | Int of int
  | Str of int
  | Op of int * int
  | Kw of int

let[@inline never] class_ t =
  match t with
  | Lparen | Rparen -> 1
  | Plus | Minus -> 2
  | Star | Slash -> 3
  | Dot -> 4
  | Eof -> 5
  | Int n -> 10 + n
  | Str _ -> 20
  | Op (a, b) -> 30 + a + b
  | Kw k -> 40 + k

let result =
  class_ (opaque Minus)
  + class_ (opaque Dot)
  + class_ (Int (opaque 3))
  + class_ (Str 0)
  + class_ (Op (1, opaque 2))
  + class_ (Kw 4)
