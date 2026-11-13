open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaValueSpec
open FlambdaWellFormedSpec
open List
open ListDef

val imports_statics : (symbol * import_class) list -> static_env

val static_names_free_in : static_env -> expr -> bool
