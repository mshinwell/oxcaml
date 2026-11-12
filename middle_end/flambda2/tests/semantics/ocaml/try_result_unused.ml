(* A handler whose body raises always. *)

external raise : exn -> 'a = "%raise"

let result = try raise Not_found with _ -> 5
