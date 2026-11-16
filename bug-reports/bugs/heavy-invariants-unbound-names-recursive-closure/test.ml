type t = Node of t list list

let rec f (Node l) = List.iter (fun x -> List.iter (fun y -> f y) x) l

let () = f (Node [ [ Node [] ] ]); print_endline "result done"
