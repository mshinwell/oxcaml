open FlambdaValidateSpec

(** val holds_from_imports : validation -> bool **)

let holds_from_imports = function
  | Same_once_lifted -> false
  | Not_validated -> false
  | _ -> true
