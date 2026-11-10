open BinNums

type variable = positive

type continuation = positive

type symbol = positive

type code_id = positive

type value_slot = positive

type naked_number_kind =
  | Kind_naked_immediate
  | Kind_naked_float32
  | Kind_naked_float
  | Kind_naked_int8
  | Kind_naked_int16
  | Kind_naked_int32
  | Kind_naked_int64
  | Kind_naked_nativeint
  | Kind_naked_vec128
  | Kind_naked_vec256
  | Kind_naked_vec512
  | Kind_naked_mask

type flambda_kind =
  | Value
  | Naked_number of naked_number_kind
  | Region
  | Rec_info

type const =
  | Naked_immediate of coq_Z
  | Tagged_immediate of coq_Z
  | Naked_float32 of coq_Z
  | Naked_float of coq_Z
  | Naked_int8 of coq_Z
  | Naked_int16 of coq_Z
  | Naked_int32 of coq_Z
  | Naked_int64 of coq_Z
  | Naked_nativeint of coq_Z
  | Naked_vec128 of coq_Z
  | Naked_vec256 of coq_Z
  | Naked_vec512 of coq_Z
  | Naked_mask of coq_Z
  | Null
  | Poison of flambda_kind

val kind_of_const : const -> flambda_kind

type simple =
  | Var of variable
  | Symbol of symbol
  | Const of const

type prim = Obj.t

type named =
  | Simple of simple
  | Prim of prim * simple list
  | Set_of_closures of code_id * (value_slot * simple) list
  | Project_value_slot of value_slot * simple

type static_const =
  | Static_const_set_of_closures of code_id * (value_slot * simple) list
  | Static_const_block of coq_Z * simple list
  | Static_const_boxed_number of simple
  | Static_const_immutable_string of coq_Z list

type apply_cont =
  { ac_continuation : continuation;
    ac_args : simple list
  }

type call_kind =
  | Direct of code_id
  | Indirect

type apply_expr =
  { ap_callee : simple;
    ap_call_kind : call_kind;
    ap_args : simple list;
    ap_continuation : continuation;
    ap_exn_continuation : continuation
  }

type expr =
  | Let of variable * named * expr
  | Let_static of static_binding list * expr
  | Let_cont_non_recursive of continuation * continuation_handler * expr
  | Let_cont_recursive of (continuation * continuation_handler) list * expr
  | Apply of apply_expr
  | Apply_cont of apply_cont
  | Switch of simple * (coq_Z * apply_cont) list
  | Invalid

and continuation_handler = Handler of variable list * expr

and static_binding =
  | Bind_code of code_id * code
  | Bind_deleted_code of code_id
  | Bind_symbol of symbol * static_const

and code =
  | Code of variable list * variable * continuation * continuation * expr

val code_params : code -> variable list

val code_my_closure : code -> variable

val code_return_continuation : code -> continuation

val code_exn_continuation : code -> continuation

val code_body : code -> expr
