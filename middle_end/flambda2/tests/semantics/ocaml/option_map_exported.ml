(* An exported function that matches on an option and calls its argument. *)

let map f o = match o with None -> None | Some x -> Some (f x)
