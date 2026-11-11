open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

type dropped =
  { dropped_symbols : symbol list;
    dropped_code : code_id list
  }

val symbol_kept : dropped -> symbol -> bool

val code_kept : dropped -> code_id -> bool

val function_decls_avoid : dropped -> (function_slot * code_id) list -> bool

val closure_symbols_avoid : dropped -> (function_slot * symbol) list -> bool

val simple_avoids : dropped -> simple -> bool

val simples_avoid : dropped -> simple list -> bool

val value_slots_avoid : dropped -> (value_slot * simple) list -> bool

val named_avoids : dropped -> named -> bool

val static_const_avoids : dropped -> static_const -> bool

val apply_cont_avoids : dropped -> apply_cont -> bool

val apply_avoids : dropped -> apply_expr -> bool

val expr_avoids : dropped -> expr -> bool

val handler_avoids : dropped -> continuation_handler -> bool

val binding_avoids : dropped -> static_binding -> bool

val code_avoids : dropped -> code -> bool

val binding_kept : dropped -> static_binding -> bool

val keep_map : ('a1 -> bool) -> ('a1 -> 'a1) -> 'a1 list -> 'a1 list

val erase_expr : dropped -> expr -> expr

val erase_handler : dropped -> continuation_handler -> continuation_handler

val erase_binding : dropped -> static_binding -> static_binding

val erase_code : dropped -> code -> code

val drop_statics : dropped -> expr -> expr option
