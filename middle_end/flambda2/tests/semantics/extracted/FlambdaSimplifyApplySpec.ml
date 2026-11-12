open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaValueSpec
open List

(** val closure_of_set_type : function_slot -> (function_slot * code_id) list ->
    value_slot list -> flambda_type list -> flambda_type **)

let closure_of_set_type slot function_decls slots tys =
  exactly_this_closure slot
    (map_values
       (fun code -> Or_unknown.Known { function_type_code_id = code })
       function_decls)
    [] (combine slots tys) Alloc_mode.Heap_or_local

(** val set_of_closures_type : code_id -> value_slot list -> flambda_type list
    -> flambda_type **)

let set_of_closures_type code slots tys =
  closure_of_set_type unnamed_function_slot
    ((unnamed_function_slot, code) :: [])
    slots tys
