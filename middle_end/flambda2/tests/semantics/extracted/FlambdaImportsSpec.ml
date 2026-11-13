open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaValueSpec
open FlambdaWellFormedSpec
open List
open ListDef

(** val imports_statics : (symbol * import_class) list -> static_env **)

let imports_statics imports =
  { static_code = [];
    static_values =
      map
        (fun pat ->
          let s, c = pat in
          s, Static_imported c)
        imports
  }

(** val static_names_free_in : static_env -> expr -> bool **)

let static_names_free_in statics e =
  forallb
    (fun s -> negb (is_bound s statics.static_values))
    (static_names symbols_of_binding e)
  && forallb
       (fun id -> negb (is_bound id statics.static_code))
       (static_names code_ids_of_binding e)
