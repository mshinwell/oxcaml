(* Two local functions that call each other, defined in one arm of a match, each
   given to an inlined function there. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

let run o n =
  match o with
  | None -> n
  | Some k ->
    let rec down j = if j = 0 then k else up (j - 1)
    and up j = if j = 0 then n else down (j - 1) in
    apply down 2 + apply up 3

let result = run (opaque (Some 3)) 4 + run None 2
