(** val sort_uniq : int list -> int list **)

let sort_uniq = List.sort_uniq Int.compare

(** val map_opt : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec map_opt f = function
  | [] -> Some []
  | x :: l0 -> (
    match f x with
    | Some y -> (
      match map_opt f l0 with Some l1 -> Some (y :: l1) | None -> None)
    | None -> None)

(** val filter_map_opt : ('a1 -> 'a2 option option) -> 'a1 list -> 'a2 list
    option **)

let rec filter_map_opt f = function
  | [] -> Some []
  | x :: l0 -> (
    match f x with
    | Some y -> (
      match filter_map_opt f l0 with
      | Some l1 -> Some (match y with Some y0 -> y0 :: l1 | None -> l1)
      | None -> None)
    | None -> None)
