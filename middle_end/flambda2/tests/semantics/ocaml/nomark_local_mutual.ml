(* As [fun_local_mutual_to_inlined], the function that applies its argument
   having no mark. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let apply f x = f x

let run n =
  let rec down k = if k = 0 then n else up (k - 1)
  and up k = if k = 0 then n + 1 else down (k - 1) in
  apply down 3 + apply up n

let result = run (opaque 4)
