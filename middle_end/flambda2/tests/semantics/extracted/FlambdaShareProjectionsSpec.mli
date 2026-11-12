open BinPos
open Datatypes
open FlambdaCseSpec
open FlambdaModel
open FlambdaNormaliseSpec
open List

val is_projection : named -> bool

val projected_from : named -> simple list

type projected = (variable * named) list

val forget_projected : variable -> projected -> projected

val forget_projected_vars : variable list -> projected -> projected

val projected_under_let : projected -> variable -> named -> projected

val same_projection : named -> named -> bool

val projected_by : projected -> named -> variable option

val share_projection : projected -> named -> named

val share_projections_knowing : projected -> expr -> expr

val share_projections_in_handler :
  projected -> continuation_handler -> continuation_handler

val share_known_projections : expr -> expr
