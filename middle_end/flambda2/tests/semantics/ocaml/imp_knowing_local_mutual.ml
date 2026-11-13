(* As [fun_local_mutual_to_inlined], in a unit that has an import: it exports a
   function that raises a predefined exception too. The unit is validated at the
   second asking, by a lifting, and of its two runs from its imports. *)

external raise : exn -> 'a = "%raise"

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

let run n =
  let rec down k = if k = 0 then n else up (k - 1)
  and up k = if k = 0 then n + 1 else down (k - 1) in
  apply down 3 + apply up n

let missing () = raise Not_found

let result = run (opaque 4)
