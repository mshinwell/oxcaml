(* [curry] and [uncurry] undo one another. Simplify inlines both and the
   function between them: the pair is never built. *)

external ( - ) : int -> int -> int = "%subint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] curry f a b = f (a, b)

let[@inline] uncurry f (a, b) = f a b

let result = uncurry (curry (fun (a, b) -> a - b)) (opaque 10, 4)
