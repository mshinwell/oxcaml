open BinPos
open Datatypes
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List

val shareable : prim -> bool

type computed = (variable * (prim * simple list)) list

val forget_computed : variable -> computed -> computed

val forget_computed_vars : variable list -> computed -> computed

val computed_under_let : computed -> variable -> named -> computed

val same_simples : simple list -> simple list -> bool

val computed_by : computed -> prim -> simple list -> variable option

val share_named : computed -> named -> named

val share_primitives_knowing : computed -> expr -> expr

val share_primitives_in_handler :
  computed -> continuation_handler -> continuation_handler

val share_known_primitives : expr -> expr
