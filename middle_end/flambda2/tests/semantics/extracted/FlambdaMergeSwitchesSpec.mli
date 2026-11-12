open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef
open PeanoNat

type arithmetic_kind =
  | Arithmetic_tagged
  | Arithmetic_naked

val standard_int_of_arithmetic_kind : arithmetic_kind -> standard_int

type merge_by =
  | By_tagging
  | By_tagging_and_negating
  | As_it_is
  | By_arithmetic of arithmetic_kind * coq_Z * coq_Z

type arithmetic_step =
  | Multiply_by of coq_Z
  | Add_to of coq_Z
  | Subtract_from of coq_Z

val arithmetic_steps : coq_Z -> coq_Z -> coq_Z -> arithmetic_step list

val arithmetic_step_value : coq_Z -> arithmetic_step -> coq_Z -> coq_Z option

val arithmetic_value : coq_Z -> arithmetic_step list -> coq_Z -> coq_Z option

val constant_of_arm : merge_by -> coq_Z -> const option

val merged_arguments : variable -> simple list -> simple list -> simple list

val constant_for : variable -> const -> simple -> simple

val arm_is_merged :
  merge_by -> variable -> apply_cont -> coq_Z * apply_cont -> bool

val bind_tagged : variable -> expr -> expr

val bind_negated : variable -> expr -> expr

val bind_arithmetic_step :
  standard_int -> variable -> arithmetic_step -> expr -> expr

val bind_arithmetic_steps :
  standard_int -> variable -> arithmetic_step list -> expr -> expr

val bind_arithmetic :
  arithmetic_kind -> coq_Z -> coq_Z -> variable -> expr -> expr

val first_difference : simple list -> simple list -> (const * const) option

val line_through :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> (coq_Z * coq_Z) option

val arithmetic_of_constants :
  coq_Z -> coq_Z -> const -> const -> ((arithmetic_kind * coq_Z) * coq_Z) option

val arithmetic_of_arms :
  coq_Z ->
  coq_Z ->
  simple list ->
  simple list ->
  ((arithmetic_kind * coq_Z) * coq_Z) option

val merge_switch : simple -> (coq_Z * apply_cont) list -> expr

type argument_way =
  | Same_in_every_arm of simple
  | Computed of merge_by

val argument_in_arm : coq_Z -> argument_way -> simple option

val arguments_in_arm : coq_Z -> argument_way list -> simple list option

val arm_has_ways :
  continuation -> argument_way list -> coq_Z * apply_cont -> bool

val column_of_arms : (coq_Z * simple list) list -> (coq_Z * simple) list option

val rest_of_arms : (coq_Z * simple list) list -> (coq_Z * simple list) list

val column_is_computed : merge_by -> (coq_Z * simple) list -> bool

val way_of_column : (coq_Z * simple) list -> argument_way option

val ways_of_arguments :
  nat -> (coq_Z * simple list) list -> argument_way list option

val bind_tagged_to : variable -> variable -> expr -> expr

val bind_same_to : variable -> variable -> expr -> expr

val bind_way : merge_by -> variable -> variable -> expr -> expr

val bind_ways : variable -> variable list -> argument_way list -> expr -> expr

val merged_by_ways :
  variable -> variable list -> argument_way list -> simple list

val names_usable : variable -> variable list -> argument_way list -> bool

val merge_switch_by_arguments :
  variable list -> simple -> (coq_Z * apply_cont) list -> expr option

type known_continuations = (continuation * variable list) list

val parameters_of_handler : continuation_handler -> variable list

val merge_switch_knowing :
  known_continuations -> simple -> (coq_Z * apply_cont) list -> expr

val merge_switches_knowing : known_continuations -> expr -> expr

val merge_switches : expr -> expr
