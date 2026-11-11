open BinPos
open Datatypes
open FlambdaBlockLoadSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List

type wrapping =
  | Boxed of boxable_number
  | Tagged

val wrapping_eq_dec : wrapping -> wrapping -> bool

val wrapping_eqb : wrapping -> wrapping -> bool

type known_numbers =
  { known_wrapped_vars : (variable * (wrapping * simple)) list;
    known_boxed_symbols : (symbol * const) list
  }

val no_numbers : known_numbers

val forget_wrapped_var : variable -> known_numbers -> known_numbers

val forget_wrapped_vars : variable list -> known_numbers -> known_numbers

val number_wrapped : named -> (wrapping * simple) option

val numbers_under_let : known_numbers -> variable -> named -> known_numbers

val static_number_boxed : static_binding -> (symbol * const) list

val numbers_under_statics :
  known_numbers -> static_binding list -> known_numbers

val unwrapped : known_numbers -> wrapping -> simple -> simple option

val unwrapping_of_known : known_numbers -> prim -> simple list -> simple option

val unbox_known_named : known_numbers -> named -> named

val unbox_numbers_knowing : known_numbers -> expr -> expr

val unbox_numbers_in_handler :
  known_numbers -> continuation_handler -> continuation_handler

val unbox_known_numbers : expr -> expr
