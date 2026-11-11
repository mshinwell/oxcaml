open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaPrimitiveSpec
open List
open ListDef
open PeanoNat

type name_map = (positive * positive) list

val names_match : name_map -> positive -> positive -> bool

val bind_names : positive list -> positive list -> name_map -> name_map option

val combine_names :
  positive list -> positive list -> name_map -> name_map option

val const_eq_dec : const -> const -> bool

val const_eqb : const -> const -> bool

val forall2b : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val simple_eqb : name_map -> simple -> simple -> bool

val simples_eqb : name_map -> simple list -> simple list -> bool

val value_slots_eqb :
  name_map -> (value_slot * simple) list -> (value_slot * simple) list -> bool

val names_eqb : (positive * positive) list -> (positive * positive) list -> bool

val named_eqb : name_map -> named -> named -> bool

val static_const_eqb : name_map -> static_const -> static_const -> bool

val call_kind_eqb : call_kind -> call_kind -> bool

val apply_cont_eqb : name_map -> name_map -> apply_cont -> apply_cont -> bool

val apply_eqb : name_map -> name_map -> apply_expr -> apply_expr -> bool

val expr_eqb : name_map -> name_map -> expr -> expr -> bool

val handler_eqb :
  name_map -> name_map -> continuation_handler -> continuation_handler -> bool

val binding_eqb : name_map -> static_binding -> static_binding -> bool

val code_eqb : code -> code -> bool
