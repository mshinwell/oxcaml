open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBlockLoadSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef

type known_array = simple option list

type known_arrays =
  { known_array_vars : (variable * known_array) list;
    known_array_symbols : (symbol * known_array) list
  }

val no_arrays : known_arrays

val forget_in_array : variable -> known_array -> known_array

val forget_array_var : variable -> known_arrays -> known_arrays

val forget_array_vars : variable list -> known_arrays -> known_arrays

val array_made_by : named -> known_array option

val arrays_under_let : known_arrays -> variable -> named -> known_arrays

val static_array_made : static_binding -> (symbol * known_array) list

val arrays_under_statics : known_arrays -> static_binding list -> known_arrays

val known_array_of : known_arrays -> simple -> known_array option

val length_of_known : known_array -> simple option

val element_loaded : known_array -> simple -> simple option

val of_known_array : known_arrays -> prim -> simple list -> simple option

val load_known_array_named : known_arrays -> named -> named

val load_arrays_knowing : known_arrays -> expr -> expr

val load_arrays_in_handler :
  known_arrays -> continuation_handler -> continuation_handler

val load_known_arrays : expr -> expr
