open BinNums
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open OxCamlOption

type value =
  | Value_const of const
  | Value_closure of code_id * (value_slot * value) list
  | Value_symbol of symbol
  | Value_block of coq_Z * value list
  | Value_boxed_number of const

(** val kind_of_value : value -> flambda_kind **)

let kind_of_value = function Value_const c -> kind_of_const c | _ -> Value

type statically_allocated_value =
  | Static_closure of code_id * (value_slot * value) list
  | Static_block of coq_Z * value list
  | Static_boxed_number of value
  | Static_string of coq_Z list

type static_env =
  { static_code : (code_id * code) list;
    static_values : (symbol * statically_allocated_value) list
  }

(** val empty_static_env : static_env **)

let empty_static_env = { static_code = []; static_values = [] }

(** val closure_of : static_env -> value -> (code_id * (value_slot * value)
    list) option **)

let closure_of statics = function
  | Value_closure (code0, value_slots) -> Some (code0, value_slots)
  | Value_symbol s -> (
    match lookup s statics.static_values with
    | Some s0 -> (
      match s0 with
      | Static_closure (code0, value_slots) -> Some (code0, value_slots)
      | _ -> None)
    | None -> None)
  | _ -> None

(** val block_of : static_env -> value -> (coq_Z * value list) option **)

let block_of statics = function
  | Value_symbol s -> (
    match lookup s statics.static_values with
    | Some s0 -> (
      match s0 with
      | Static_block (tag, fields) -> Some (tag, fields)
      | _ -> None)
    | None -> None)
  | Value_block (tag, fields) -> Some (tag, fields)
  | _ -> None

(** val boxable_number_of_const : const -> boxable_number option **)

let boxable_number_of_const c = boxable_number_of_kind (kind_of_const c)

(** val boxable_contents : const -> const option **)

let boxable_contents c =
  match boxable_number_of_const c with Some _ -> Some c | None -> None

(** val boxed_number_of : static_env -> value -> const option **)

let boxed_number_of statics = function
  | Value_symbol s -> (
    match lookup s statics.static_values with
    | Some s0 -> (
      match s0 with
      | Static_boxed_number contents -> (
        match contents with Value_const c -> boxable_contents c | _ -> None)
      | _ -> None)
    | None -> None)
  | Value_boxed_number c -> boxable_contents c
  | _ -> None

(** val string_of : static_env -> value -> coq_Z list option **)

let string_of statics = function
  | Value_symbol s -> (
    match lookup s statics.static_values with
    | Some s0 -> (
      match s0 with Static_string bytes -> Some bytes | _ -> None)
    | None -> None)
  | _ -> None

(** val is_allocated : static_env -> value -> bool **)

let is_allocated statics v =
  ((is_some (closure_of statics v) || is_some (block_of statics v))
  || is_some (boxed_number_of statics v))
  || is_some (string_of statics v)
