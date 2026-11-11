open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

val keep_slots :
  value_slot list -> (value_slot * 'a1) list -> (value_slot * 'a1) list

val drop_slots_static_const : value_slot list -> static_const -> static_const

val drop_slots : value_slot list -> expr -> expr

val drop_slots_handler :
  value_slot list -> continuation_handler -> continuation_handler

val drop_slots_binding : value_slot list -> static_binding -> static_binding

val drop_slots_code : value_slot list -> code -> code

val named_projects_none : value_slot list -> named -> bool

val slots_unused : value_slot list -> expr -> bool

val handler_slots_unused : value_slot list -> continuation_handler -> bool

val binding_slots_unused : value_slot list -> static_binding -> bool

val code_slots_unused : value_slot list -> code -> bool

val drop_unused_slots : value_slot list -> expr -> expr option
