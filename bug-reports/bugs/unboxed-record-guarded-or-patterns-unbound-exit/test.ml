type t = #{ a : int; b : bool }

let f (c : t) (g : int -> bool) =
  match c with
  | (#{ a = x; b = true } | #{ a = x; b = false }) when g x -> 1
  | (#{ a = y; b = true } | #{ a = y; b = false }) when g y -> 2
  | _ -> 3

let () = Printf.printf "result %d\n" (f #{ a = 5; b = true } (fun _ -> false))
