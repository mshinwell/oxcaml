(** val is_some : 'a1 option -> bool **)

let is_some = function Some _ -> true | None -> false
