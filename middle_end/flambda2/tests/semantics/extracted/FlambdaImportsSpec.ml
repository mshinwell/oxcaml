open FlambdaModel
open FlambdaValueSpec
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
