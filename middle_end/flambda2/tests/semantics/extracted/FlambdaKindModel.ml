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

(** val kind_eq_dec : flambda_kind -> flambda_kind -> bool **)

let kind_eq_dec k k' =
  match k with
  | Value -> ( match k' with Value -> true | _ -> false)
  | Naked_number k0 -> (
    match k' with
    | Naked_number k1 -> (
      match k0 with
      | Kind_naked_immediate -> (
        match k1 with Kind_naked_immediate -> true | _ -> false)
      | Kind_naked_float32 -> (
        match k1 with Kind_naked_float32 -> true | _ -> false)
      | Kind_naked_float -> (
        match k1 with Kind_naked_float -> true | _ -> false)
      | Kind_naked_int8 -> (
        match k1 with Kind_naked_int8 -> true | _ -> false)
      | Kind_naked_int16 -> (
        match k1 with Kind_naked_int16 -> true | _ -> false)
      | Kind_naked_int32 -> (
        match k1 with Kind_naked_int32 -> true | _ -> false)
      | Kind_naked_int64 -> (
        match k1 with Kind_naked_int64 -> true | _ -> false)
      | Kind_naked_nativeint -> (
        match k1 with Kind_naked_nativeint -> true | _ -> false)
      | Kind_naked_vec128 -> (
        match k1 with Kind_naked_vec128 -> true | _ -> false)
      | Kind_naked_vec256 -> (
        match k1 with Kind_naked_vec256 -> true | _ -> false)
      | Kind_naked_vec512 -> (
        match k1 with Kind_naked_vec512 -> true | _ -> false)
      | Kind_naked_mask -> (
        match k1 with Kind_naked_mask -> true | _ -> false))
    | _ -> false)
  | Region -> ( match k' with Region -> true | _ -> false)
  | Rec_info -> ( match k' with Rec_info -> true | _ -> false)

(** val kind_eqb : flambda_kind -> flambda_kind -> bool **)

let kind_eqb k k' = if kind_eq_dec k k' then true else false

type standard_int =
  | Standard_tagged_immediate
  | Standard_naked_immediate
  | Standard_naked_int8
  | Standard_naked_int16
  | Standard_naked_int32
  | Standard_naked_int64
  | Standard_naked_nativeint

type boxable_number =
  | Boxable_naked_float32
  | Boxable_naked_float
  | Boxable_naked_int32
  | Boxable_naked_int64
  | Boxable_naked_nativeint
  | Boxable_naked_vec128
  | Boxable_naked_vec256
  | Boxable_naked_vec512
  | Boxable_naked_mask

(** val boxable_number_of_kind : flambda_kind -> boxable_number option **)

let boxable_number_of_kind = function
  | Naked_number k0 -> (
    match k0 with
    | Kind_naked_float32 -> Some Boxable_naked_float32
    | Kind_naked_float -> Some Boxable_naked_float
    | Kind_naked_int32 -> Some Boxable_naked_int32
    | Kind_naked_int64 -> Some Boxable_naked_int64
    | Kind_naked_nativeint -> Some Boxable_naked_nativeint
    | Kind_naked_vec128 -> Some Boxable_naked_vec128
    | Kind_naked_vec256 -> Some Boxable_naked_vec256
    | Kind_naked_vec512 -> Some Boxable_naked_vec512
    | Kind_naked_mask -> Some Boxable_naked_mask
    | _ -> None)
  | _ -> None
