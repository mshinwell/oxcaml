open BinNums
open FlambdaKindModel
open FlambdaPrimitiveModel

type variable = positive

type continuation = positive

type symbol = positive

type code_id = positive

type value_slot = positive

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

(** val kind_of_const : const -> flambda_kind **)

let kind_of_const = function
  | Naked_immediate _ -> Naked_number Kind_naked_immediate
  | Naked_float32 _ -> Naked_number Kind_naked_float32
  | Naked_float _ -> Naked_number Kind_naked_float
  | Naked_int8 _ -> Naked_number Kind_naked_int8
  | Naked_int16 _ -> Naked_number Kind_naked_int16
  | Naked_int32 _ -> Naked_number Kind_naked_int32
  | Naked_int64 _ -> Naked_number Kind_naked_int64
  | Naked_nativeint _ -> Naked_number Kind_naked_nativeint
  | Naked_vec128 _ -> Naked_number Kind_naked_vec128
  | Naked_vec256 _ -> Naked_number Kind_naked_vec256
  | Naked_vec512 _ -> Naked_number Kind_naked_vec512
  | Naked_mask _ -> Naked_number Kind_naked_mask
  | Poison kind -> kind
  | _ -> Value

type simple =
  | Var of variable
  | Symbol of symbol
  | Const of const

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

(** val code_params : code -> variable list **)

let code_params = function Code (params, _, _, _, _) -> params

(** val code_my_closure : code -> variable **)

let code_my_closure = function Code (_, my_closure, _, _, _) -> my_closure

(** val code_return_continuation : code -> continuation **)

let code_return_continuation = function
  | Code (_, _, return_continuation, _, _) -> return_continuation

(** val code_exn_continuation : code -> continuation **)

let code_exn_continuation = function
  | Code (_, _, _, exn_continuation, _) -> exn_continuation

(** val code_body : code -> expr **)

let code_body = function Code (_, _, _, _, body) -> body
