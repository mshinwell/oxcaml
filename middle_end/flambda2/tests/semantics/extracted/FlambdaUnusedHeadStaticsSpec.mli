open Datatypes
open FlambdaLiftSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaUnusedStaticsSpec
open FlambdaWellFormedSpec
open List
open ListDef

val head_bindings : expr -> static_binding list

val under_head : expr -> expr

val value_slots_plain : (value_slot * simple) list -> bool

val static_const_total : static_const -> bool

val removed_binding_total : dropped -> static_binding -> bool

val kept_code_binds_only_kept : dropped -> static_binding -> bool

val head_statics_removable : dropped -> expr -> bool

val table_binding : symbol * simple list -> static_binding

val tables_dropped : (symbol * simple list) list -> dropped

val tables_plain : (symbol * simple list) list -> bool

val add_head_tables : (symbol * simple list) list -> expr -> expr
