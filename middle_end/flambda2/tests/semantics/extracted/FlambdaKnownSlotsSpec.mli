open BinPos
open Datatypes
open FlambdaKnownSymbolsSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaStaticsInScopeSpec
open FlambdaWellFormedSpec
open List
open ListDef

type known_slots = (value_slot * simple) list

val same_simple : simple -> simple -> bool

val closed_slots : known_slots -> bool

val named_slots_made : named -> (value_slot * simple) list

val static_const_slots_made : static_const -> (value_slot * simple) list

val slots_made : expr -> (value_slot * simple) list

val handler_slots_made : continuation_handler -> (value_slot * simple) list

val binding_slots_made : static_binding -> (value_slot * simple) list

val code_slots_made : code -> (value_slot * simple) list

val slots_known : (value_slot * simple) list -> known_slots

val value_slots_as : known_slots -> (value_slot * simple) list -> bool

val slots_as : known_slots -> expr -> bool

val handler_slots_as : known_slots -> continuation_handler -> bool

val binding_slots_as : known_slots -> static_binding -> bool

val code_slots_as : known_slots -> code -> bool

val read_slot : known_slots -> symbol list -> named -> named

val read_slots : known_slots -> symbol list -> expr -> expr

val read_slots_in_handler :
  known_slots -> symbol list -> continuation_handler -> continuation_handler

val read_slots_in_binding :
  known_slots -> symbol list -> static_binding -> static_binding

val read_slots_in_code : known_slots -> symbol list -> code -> code

val read_known_slots : expr -> expr
