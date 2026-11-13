open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaMergeSwitchesSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open FlambdaSemanticsSpec
open List
open ListDef
open OxCamlOption
open PeanoNat

type known_tables = (symbol * simple list) list

val element_closed : simple -> bool

val table_of_binding : static_binding -> known_tables

val tables_under_statics : known_tables -> static_binding list -> known_tables

val table_offset : coq_Z -> coq_Z

val table_index : coq_Z -> coq_Z -> coq_Z -> coq_Z option

val table_element : coq_Z -> coq_Z -> simple list -> coq_Z -> simple option

val all_immediates : simple list -> bool

val table_array_kind : bool -> array_kind

val table_load_kind : bool -> array_load_kind

val element_taken : bool -> simple -> bool

val element_for : variable -> simple -> simple -> simple

val merged_across :
  variable -> simple list -> (coq_Z * apply_cont) list -> simple list

val arm_is_loaded :
  variable ->
  apply_cont ->
  coq_Z ->
  coq_Z ->
  simple list ->
  bool ->
  coq_Z * apply_cont ->
  bool

val bind_table_offset : variable -> coq_Z -> coq_Z -> expr -> expr

val bind_table_load :
  variable -> symbol -> coq_Z -> coq_Z -> bool -> expr -> expr

val table_has_arms :
  variable ->
  apply_cont ->
  coq_Z ->
  coq_Z ->
  (coq_Z * apply_cont) list ->
  symbol * simple list ->
  bool

val merge_switch_by_table :
  known_tables -> simple -> (coq_Z * apply_cont) list -> expr option

type table_way =
  | Without_table of argument_way
  | From_table of symbol * simple list * bool

val is_from_table : table_way -> bool

val argument_by_table_way :
  coq_Z -> coq_Z -> coq_Z -> table_way -> simple option

val arguments_by_table_ways :
  coq_Z -> coq_Z -> coq_Z -> table_way list -> simple list option

val arm_has_table_ways :
  continuation -> coq_Z -> coq_Z -> table_way list -> coq_Z * apply_cont -> bool

val table_has_column :
  coq_Z -> coq_Z -> (coq_Z * simple) list -> symbol * simple list -> bool

val table_way_of_column :
  known_tables -> coq_Z -> coq_Z -> (coq_Z * simple) list -> table_way option

val table_ways_of_arguments :
  known_tables ->
  coq_Z ->
  coq_Z ->
  nat ->
  (coq_Z * simple list) list ->
  table_way list option

val bind_table_load_to :
  variable -> variable -> symbol -> coq_Z -> coq_Z -> bool -> expr -> expr

val bind_table_way :
  coq_Z -> coq_Z -> variable -> variable -> table_way -> expr -> expr

val bind_table_ways :
  coq_Z -> coq_Z -> variable -> variable list -> table_way list -> expr -> expr

val merged_by_table_way : variable -> variable -> table_way -> simple

val merged_by_table_ways :
  variable -> variable list -> table_way list -> simple list

val table_names_usable : variable -> variable list -> table_way list -> bool

val merge_switch_by_table_ways :
  known_continuations ->
  known_tables ->
  simple ->
  (coq_Z * apply_cont) list ->
  expr option

val merge_switch_with_tables :
  known_continuations ->
  known_tables ->
  simple ->
  (coq_Z * apply_cont) list ->
  expr

val merge_tables_under : known_continuations -> known_tables -> expr -> expr

val merge_tables_in_handler :
  known_continuations ->
  known_tables ->
  continuation_handler ->
  continuation_handler

val merge_tables_knowing : known_tables -> expr -> expr

val merge_tables_in_code : known_tables -> expr -> expr

val merge_tables_in_code_in_handler :
  known_tables -> continuation_handler -> continuation_handler

val merge_tables : expr -> expr
