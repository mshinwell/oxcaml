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

val kind_eq_dec : flambda_kind -> flambda_kind -> bool

val kind_eqb : flambda_kind -> flambda_kind -> bool

type standard_int =
  | Standard_tagged_immediate
  | Standard_naked_immediate
  | Standard_naked_int8
  | Standard_naked_int16
  | Standard_naked_int32
  | Standard_naked_int64
  | Standard_naked_nativeint

val kind_of_standard_int : standard_int -> flambda_kind

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

val unboxed_kind : boxable_number -> flambda_kind

val boxable_number_of_kind : flambda_kind -> boxable_number option
