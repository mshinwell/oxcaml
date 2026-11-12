(* Functions on options, as a small library has them. *)

let map f o = match o with None -> None | Some x -> Some (f x)

let default d o = match o with None -> d | Some x -> x

let is_some o = match o with None -> false | Some _ -> true
