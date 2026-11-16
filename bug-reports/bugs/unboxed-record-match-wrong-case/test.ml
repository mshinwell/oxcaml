type t = #{ a : int }

let f (c : #(bool * t * bool)) =
  match c with
  | #(true, #{ a = 0 }, _) -> 1
  | #(false, _, true) -> 2
  | #(_, (#{ a = 2 } | #{ a = _ }), false) -> 4
  | _ -> 5

let () = Printf.printf "result %d\n" (f #(true, #{ a = 1 }, true))
