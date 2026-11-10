(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x :: tl -> (
    match l' with [] -> [] | y :: tl' -> (x, y) :: combine tl tl')
