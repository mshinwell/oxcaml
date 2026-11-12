open FlambdaValidateSpec

(** val holds_from_imports : validation -> bool **)

let holds_from_imports = function
  | Same_up_to_bound_names -> true
  | Same_once_normalised -> true
  | Same_once_unused_statics_removed -> true
  | _ -> false
