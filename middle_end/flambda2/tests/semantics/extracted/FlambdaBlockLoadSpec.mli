open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef

type known_block = coq_Z * simple option list

type known_blocks =
  { known_vars : (variable * known_block) list;
    known_symbols : (symbol * known_block) list
  }

val no_blocks : known_blocks

val forget_field : variable -> simple option -> simple option

val forget_in_block : variable -> known_block -> known_block

val forget_var : variable -> known_blocks -> known_blocks

val forget_vars : variable list -> known_blocks -> known_blocks

val block_made : named -> known_block option

val known_under_let : known_blocks -> variable -> named -> known_blocks

val static_block_made : static_binding -> (symbol * known_block) list

val known_under_statics : known_blocks -> static_binding list -> known_blocks

val known_block_of : known_blocks -> simple -> known_block option

val field_loaded : block_access_kind -> coq_Z -> known_block -> simple option

val of_known_block : unary_primitive -> known_block -> simple option

val unary_applied : prim -> simple list -> (unary_primitive * simple) option

val load_known_named : known_blocks -> named -> named

val load_blocks_knowing : known_blocks -> expr -> expr

val load_blocks_in_handler :
  known_blocks -> continuation_handler -> continuation_handler

val load_known_blocks : expr -> expr
