open BinInt
open BinNums
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaPrimitiveModel
open FlambdaValueSpec
open OxCamlOption

(** val in_range : coq_Z -> coq_Z -> bool **)

let in_range width z =
  Z.leb (Z.opp (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub width (Zpos Coq_xH)))) z
  && Z.ltb z (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub width (Zpos Coq_xH)))

(** val wrap : coq_Z -> coq_Z -> coq_Z **)

let wrap width z =
  Z.sub
    (Z.modulo
       (Z.add z (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub width (Zpos Coq_xH))))
       (Z.pow (Zpos (Coq_xO Coq_xH)) width))
    (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub width (Zpos Coq_xH)))

(** val unsigned : coq_Z -> coq_Z -> coq_Z **)

let unsigned width z =
  if Z.ltb z Z0 then Z.add z (Z.pow (Zpos (Coq_xO Coq_xH)) width) else z

(** val reading : coq_Z -> signedness -> coq_Z -> coq_Z **)

let reading width s z =
  match s with Signed -> z | Unsigned -> unsigned width z

(** val int_width : standard_int -> coq_Z **)

let int_width = function
  | Standard_tagged_immediate ->
    Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
  | Standard_naked_immediate ->
    Zpos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
  | Standard_naked_int8 -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
  | Standard_naked_int16 -> Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
  | Standard_naked_int32 ->
    Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
  | _ -> Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))

(** val const_of_int : standard_int -> coq_Z -> const **)

let const_of_int kind i =
  match kind with
  | Standard_tagged_immediate -> Tagged_immediate i
  | Standard_naked_immediate -> Naked_immediate i
  | Standard_naked_int8 -> Naked_int8 i
  | Standard_naked_int16 -> Naked_int16 i
  | Standard_naked_int32 -> Naked_int32 i
  | Standard_naked_int64 -> Naked_int64 i
  | Standard_naked_nativeint -> Naked_nativeint i

(** val int_of_value : standard_int -> value -> coq_Z option **)

let int_of_value kind v =
  match kind with
  | Standard_tagged_immediate -> (
    match v with
    | Value_const c -> (
      match c with
      | Tagged_immediate i ->
        if in_range (int_width kind) i then Some i else None
      | _ -> None)
    | _ -> None)
  | Standard_naked_immediate -> (
    match v with
    | Value_const c -> (
      match c with
      | Naked_immediate i ->
        if in_range (int_width kind) i then Some i else None
      | _ -> None)
    | _ -> None)
  | Standard_naked_int8 -> (
    match v with
    | Value_const c -> (
      match c with
      | Naked_int8 i -> if in_range (int_width kind) i then Some i else None
      | _ -> None)
    | _ -> None)
  | Standard_naked_int16 -> (
    match v with
    | Value_const c -> (
      match c with
      | Naked_int16 i -> if in_range (int_width kind) i then Some i else None
      | _ -> None)
    | _ -> None)
  | Standard_naked_int32 -> (
    match v with
    | Value_const c -> (
      match c with
      | Naked_int32 i -> if in_range (int_width kind) i then Some i else None
      | _ -> None)
    | _ -> None)
  | Standard_naked_int64 -> (
    match v with
    | Value_const c -> (
      match c with
      | Naked_int64 i -> if in_range (int_width kind) i then Some i else None
      | _ -> None)
    | _ -> None)
  | Standard_naked_nativeint -> (
    match v with
    | Value_const c -> (
      match c with
      | Naked_nativeint i ->
        if in_range (int_width kind) i then Some i else None
      | _ -> None)
    | _ -> None)

(** val eval_int_arith : coq_Z -> binary_int_arith_op -> coq_Z -> coq_Z -> coq_Z
    option **)

let eval_int_arith width op a b =
  match op with
  | Add -> Some (wrap width (Z.add a b))
  | Sub -> Some (wrap width (Z.sub a b))
  | Mul -> Some (wrap width (Z.mul a b))
  | Div s ->
    if Z.eqb b Z0
    then None
    else Some (wrap width (Z.quot (reading width s a) (reading width s b)))
  | Mod s ->
    if Z.eqb b Z0
    then None
    else Some (wrap width (Z.rem (reading width s a) (reading width s b)))
  | And -> Some (wrap width (Z.coq_land a b))
  | Or -> Some (wrap width (Z.coq_lor a b))
  | Xor -> Some (wrap width (Z.coq_lxor a b))

(** val eval_int_comparison : coq_Z -> int_comparison -> coq_Z -> coq_Z -> bool
    **)

let eval_int_comparison width c a b =
  match c with
  | Int_eq -> Z.eqb a b
  | Int_neq -> negb (Z.eqb a b)
  | Int_lt s -> Z.ltb (reading width s a) (reading width s b)
  | Int_gt s -> Z.ltb (reading width s b) (reading width s a)
  | Int_le s -> Z.leb (reading width s a) (reading width s b)
  | Int_ge s -> Z.leb (reading width s b) (reading width s a)

(** val eval_int_comp : coq_Z -> int_comparison_behaviour -> coq_Z -> coq_Z ->
    coq_Z **)

let eval_int_comp width behaviour a b =
  match behaviour with
  | Yielding_bool c ->
    if eval_int_comparison width c a b then Zpos Coq_xH else Z0
  | Yielding_int_like_compare_functions s -> (
    match Z.compare (reading width s a) (reading width s b) with
    | Eq -> Z0
    | Lt -> Zneg Coq_xH
    | Gt -> Zpos Coq_xH)

(** val naked_bool : bool -> value **)

let naked_bool b = Value_const (Naked_immediate (if b then Zpos Coq_xH else Z0))

(** val is_tagged_immediate : value -> bool **)

let is_tagged_immediate v = is_some (int_of_value Standard_tagged_immediate v)

(** val eval_is_int : static_env -> bool -> value -> bool option **)

let eval_is_int statics variant_only v =
  if is_tagged_immediate v
  then Some true
  else if
    if variant_only
    then is_some (block_of statics v)
    else is_allocated statics v
  then Some false
  else None

(** val eval_is_null : static_env -> value -> bool option **)

let eval_is_null statics v =
  match v with
  | Value_const c -> (
    match c with
    | Null -> Some true
    | _ ->
      if is_tagged_immediate v || is_allocated statics v
      then Some false
      else None)
  | _ ->
    if is_tagged_immediate v || is_allocated statics v then Some false else None

(** val is_number_of_kind : boxable_number -> const -> bool **)

let is_number_of_kind kind c =
  match kind with
  | Boxable_naked_float32 -> (
    match c with Naked_float32 _ -> true | _ -> false)
  | Boxable_naked_float -> ( match c with Naked_float _ -> true | _ -> false)
  | Boxable_naked_int32 -> ( match c with Naked_int32 _ -> true | _ -> false)
  | Boxable_naked_int64 -> ( match c with Naked_int64 _ -> true | _ -> false)
  | Boxable_naked_nativeint -> (
    match c with Naked_nativeint _ -> true | _ -> false)
  | Boxable_naked_vec128 -> (
    match c with Naked_vec128 _ -> true | _ -> false)
  | Boxable_naked_vec256 -> (
    match c with Naked_vec256 _ -> true | _ -> false)
  | Boxable_naked_vec512 -> (
    match c with Naked_vec512 _ -> true | _ -> false)
  | Boxable_naked_mask -> ( match c with Naked_mask _ -> true | _ -> false)

(** val eval_unary_primitive : static_env -> unary_primitive -> value -> value
    option **)

let eval_unary_primitive statics p v =
  match p with
  | Is_int variant_only ->
    option_map naked_bool (eval_is_int statics variant_only v)
  | Is_null -> option_map naked_bool (eval_is_null statics v)
  | Get_tag -> (
    match block_of statics v with
    | Some p0 ->
      let tag, _ = p0 in
      Some (Value_const (Naked_immediate tag))
    | None -> None)
  | Opaque_identity kind ->
    if kind_eqb (kind_of_value v) kind then Some v else None
  | Unbox_number kind -> (
    match boxed_number_of statics v with
    | Some c -> if is_number_of_kind kind c then Some (Value_const c) else None
    | None -> None)
  | Box_number kind -> (
    match v with
    | Value_const c ->
      if is_number_of_kind kind c then Some (Value_boxed_number c) else None
    | _ -> None)
  | Untag_immediate -> (
    match int_of_value Standard_tagged_immediate v with
    | Some i -> Some (Value_const (Naked_immediate i))
    | None -> None)
  | Tag_immediate -> (
    match int_of_value Standard_naked_immediate v with
    | Some i -> Some (Value_const (Tagged_immediate i))
    | None -> None)

(** val eval_binary_primitive : binary_primitive -> value -> value -> value
    option **)

let eval_binary_primitive p v1 v2 =
  match p with
  | Int_arith (kind, op) -> (
    match int_of_value kind v1 with
    | Some a -> (
      match int_of_value kind v2 with
      | Some b -> (
        match eval_int_arith (int_width kind) op a b with
        | Some result -> Some (Value_const (const_of_int kind result))
        | None -> None)
      | None -> None)
    | None -> None)
  | Int_comp (kind, behaviour) -> (
    match int_of_value kind v1 with
    | Some a -> (
      match int_of_value kind v2 with
      | Some b ->
        Some
          (Value_const
             (Naked_immediate (eval_int_comp (int_width kind) behaviour a b)))
      | None -> None)
    | None -> None)

(** val eval_prim : static_env -> prim -> value list -> value option **)

let eval_prim statics p vs =
  match p with
  | Unary p0 -> (
    match vs with
    | [] -> None
    | v :: l -> (
      match l with [] -> eval_unary_primitive statics p0 v | _ :: _ -> None))
  | Binary p0 -> (
    match vs with
    | [] -> None
    | v1 :: l -> (
      match l with
      | [] -> None
      | v2 :: l0 -> (
        match l0 with [] -> eval_binary_primitive p0 v1 v2 | _ :: _ -> None)))

(** val prim_eq_dec : prim -> prim -> bool **)

let prim_eq_dec p p' =
  match p with
  | Unary p0 -> (
    match p' with
    | Unary p1 -> (
      match p0 with
      | Is_int variant_only -> (
        match p1 with
        | Is_int variant_only0 ->
          if variant_only
          then if variant_only0 then true else false
          else if variant_only0
          then false
          else true
        | _ -> false)
      | Is_null -> ( match p1 with Is_null -> true | _ -> false)
      | Get_tag -> ( match p1 with Get_tag -> true | _ -> false)
      | Opaque_identity kind -> (
        match p1 with
        | Opaque_identity kind0 -> (
          match kind with
          | Value -> ( match kind0 with Value -> true | _ -> false)
          | Naked_number k -> (
            match kind0 with
            | Naked_number k0 -> (
              match k with
              | Kind_naked_immediate -> (
                match k0 with Kind_naked_immediate -> true | _ -> false)
              | Kind_naked_float32 -> (
                match k0 with Kind_naked_float32 -> true | _ -> false)
              | Kind_naked_float -> (
                match k0 with Kind_naked_float -> true | _ -> false)
              | Kind_naked_int8 -> (
                match k0 with Kind_naked_int8 -> true | _ -> false)
              | Kind_naked_int16 -> (
                match k0 with Kind_naked_int16 -> true | _ -> false)
              | Kind_naked_int32 -> (
                match k0 with Kind_naked_int32 -> true | _ -> false)
              | Kind_naked_int64 -> (
                match k0 with Kind_naked_int64 -> true | _ -> false)
              | Kind_naked_nativeint -> (
                match k0 with Kind_naked_nativeint -> true | _ -> false)
              | Kind_naked_vec128 -> (
                match k0 with Kind_naked_vec128 -> true | _ -> false)
              | Kind_naked_vec256 -> (
                match k0 with Kind_naked_vec256 -> true | _ -> false)
              | Kind_naked_vec512 -> (
                match k0 with Kind_naked_vec512 -> true | _ -> false)
              | Kind_naked_mask -> (
                match k0 with Kind_naked_mask -> true | _ -> false))
            | _ -> false)
          | Region -> ( match kind0 with Region -> true | _ -> false)
          | Rec_info -> ( match kind0 with Rec_info -> true | _ -> false))
        | _ -> false)
      | Unbox_number kind -> (
        match p1 with
        | Unbox_number kind0 -> (
          match kind with
          | Boxable_naked_float32 -> (
            match kind0 with Boxable_naked_float32 -> true | _ -> false)
          | Boxable_naked_float -> (
            match kind0 with Boxable_naked_float -> true | _ -> false)
          | Boxable_naked_int32 -> (
            match kind0 with Boxable_naked_int32 -> true | _ -> false)
          | Boxable_naked_int64 -> (
            match kind0 with Boxable_naked_int64 -> true | _ -> false)
          | Boxable_naked_nativeint -> (
            match kind0 with Boxable_naked_nativeint -> true | _ -> false)
          | Boxable_naked_vec128 -> (
            match kind0 with Boxable_naked_vec128 -> true | _ -> false)
          | Boxable_naked_vec256 -> (
            match kind0 with Boxable_naked_vec256 -> true | _ -> false)
          | Boxable_naked_vec512 -> (
            match kind0 with Boxable_naked_vec512 -> true | _ -> false)
          | Boxable_naked_mask -> (
            match kind0 with Boxable_naked_mask -> true | _ -> false))
        | _ -> false)
      | Box_number kind -> (
        match p1 with
        | Box_number kind0 -> (
          match kind with
          | Boxable_naked_float32 -> (
            match kind0 with Boxable_naked_float32 -> true | _ -> false)
          | Boxable_naked_float -> (
            match kind0 with Boxable_naked_float -> true | _ -> false)
          | Boxable_naked_int32 -> (
            match kind0 with Boxable_naked_int32 -> true | _ -> false)
          | Boxable_naked_int64 -> (
            match kind0 with Boxable_naked_int64 -> true | _ -> false)
          | Boxable_naked_nativeint -> (
            match kind0 with Boxable_naked_nativeint -> true | _ -> false)
          | Boxable_naked_vec128 -> (
            match kind0 with Boxable_naked_vec128 -> true | _ -> false)
          | Boxable_naked_vec256 -> (
            match kind0 with Boxable_naked_vec256 -> true | _ -> false)
          | Boxable_naked_vec512 -> (
            match kind0 with Boxable_naked_vec512 -> true | _ -> false)
          | Boxable_naked_mask -> (
            match kind0 with Boxable_naked_mask -> true | _ -> false))
        | _ -> false)
      | Untag_immediate -> (
        match p1 with Untag_immediate -> true | _ -> false)
      | Tag_immediate -> ( match p1 with Tag_immediate -> true | _ -> false))
    | Binary _ -> false)
  | Binary p0 -> (
    match p' with
    | Unary _ -> false
    | Binary p1 -> (
      match p0 with
      | Int_arith (kind, op) -> (
        match p1 with
        | Int_arith (kind0, op0) -> (
          match kind with
          | Standard_tagged_immediate -> (
            match kind0 with
            | Standard_tagged_immediate -> (
              match op with
              | Add -> ( match op0 with Add -> true | _ -> false)
              | Sub -> ( match op0 with Sub -> true | _ -> false)
              | Mul -> ( match op0 with Mul -> true | _ -> false)
              | Div s -> (
                match op0 with
                | Div s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | Mod s -> (
                match op0 with
                | Mod s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | And -> ( match op0 with And -> true | _ -> false)
              | Or -> ( match op0 with Or -> true | _ -> false)
              | Xor -> ( match op0 with Xor -> true | _ -> false))
            | _ -> false)
          | Standard_naked_immediate -> (
            match kind0 with
            | Standard_naked_immediate -> (
              match op with
              | Add -> ( match op0 with Add -> true | _ -> false)
              | Sub -> ( match op0 with Sub -> true | _ -> false)
              | Mul -> ( match op0 with Mul -> true | _ -> false)
              | Div s -> (
                match op0 with
                | Div s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | Mod s -> (
                match op0 with
                | Mod s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | And -> ( match op0 with And -> true | _ -> false)
              | Or -> ( match op0 with Or -> true | _ -> false)
              | Xor -> ( match op0 with Xor -> true | _ -> false))
            | _ -> false)
          | Standard_naked_int8 -> (
            match kind0 with
            | Standard_naked_int8 -> (
              match op with
              | Add -> ( match op0 with Add -> true | _ -> false)
              | Sub -> ( match op0 with Sub -> true | _ -> false)
              | Mul -> ( match op0 with Mul -> true | _ -> false)
              | Div s -> (
                match op0 with
                | Div s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | Mod s -> (
                match op0 with
                | Mod s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | And -> ( match op0 with And -> true | _ -> false)
              | Or -> ( match op0 with Or -> true | _ -> false)
              | Xor -> ( match op0 with Xor -> true | _ -> false))
            | _ -> false)
          | Standard_naked_int16 -> (
            match kind0 with
            | Standard_naked_int16 -> (
              match op with
              | Add -> ( match op0 with Add -> true | _ -> false)
              | Sub -> ( match op0 with Sub -> true | _ -> false)
              | Mul -> ( match op0 with Mul -> true | _ -> false)
              | Div s -> (
                match op0 with
                | Div s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | Mod s -> (
                match op0 with
                | Mod s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | And -> ( match op0 with And -> true | _ -> false)
              | Or -> ( match op0 with Or -> true | _ -> false)
              | Xor -> ( match op0 with Xor -> true | _ -> false))
            | _ -> false)
          | Standard_naked_int32 -> (
            match kind0 with
            | Standard_naked_int32 -> (
              match op with
              | Add -> ( match op0 with Add -> true | _ -> false)
              | Sub -> ( match op0 with Sub -> true | _ -> false)
              | Mul -> ( match op0 with Mul -> true | _ -> false)
              | Div s -> (
                match op0 with
                | Div s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | Mod s -> (
                match op0 with
                | Mod s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | And -> ( match op0 with And -> true | _ -> false)
              | Or -> ( match op0 with Or -> true | _ -> false)
              | Xor -> ( match op0 with Xor -> true | _ -> false))
            | _ -> false)
          | Standard_naked_int64 -> (
            match kind0 with
            | Standard_naked_int64 -> (
              match op with
              | Add -> ( match op0 with Add -> true | _ -> false)
              | Sub -> ( match op0 with Sub -> true | _ -> false)
              | Mul -> ( match op0 with Mul -> true | _ -> false)
              | Div s -> (
                match op0 with
                | Div s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | Mod s -> (
                match op0 with
                | Mod s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | And -> ( match op0 with And -> true | _ -> false)
              | Or -> ( match op0 with Or -> true | _ -> false)
              | Xor -> ( match op0 with Xor -> true | _ -> false))
            | _ -> false)
          | Standard_naked_nativeint -> (
            match kind0 with
            | Standard_naked_nativeint -> (
              match op with
              | Add -> ( match op0 with Add -> true | _ -> false)
              | Sub -> ( match op0 with Sub -> true | _ -> false)
              | Mul -> ( match op0 with Mul -> true | _ -> false)
              | Div s -> (
                match op0 with
                | Div s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | Mod s -> (
                match op0 with
                | Mod s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))
                | _ -> false)
              | And -> ( match op0 with And -> true | _ -> false)
              | Or -> ( match op0 with Or -> true | _ -> false)
              | Xor -> ( match op0 with Xor -> true | _ -> false))
            | _ -> false))
        | Int_comp (_, _) -> false)
      | Int_comp (kind, behaviour) -> (
        match p1 with
        | Int_arith (_, _) -> false
        | Int_comp (kind0, behaviour0) -> (
          match kind with
          | Standard_tagged_immediate -> (
            match kind0 with
            | Standard_tagged_immediate -> (
              match behaviour with
              | Yielding_bool c -> (
                match behaviour0 with
                | Yielding_bool c0 -> (
                  match c with
                  | Int_eq -> ( match c0 with Int_eq -> true | _ -> false)
                  | Int_neq -> ( match c0 with Int_neq -> true | _ -> false)
                  | Int_lt s -> (
                    match c0 with
                    | Int_lt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_gt s -> (
                    match c0 with
                    | Int_gt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_le s -> (
                    match c0 with
                    | Int_le s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_ge s -> (
                    match c0 with
                    | Int_ge s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false))
                | Yielding_int_like_compare_functions _ -> false)
              | Yielding_int_like_compare_functions s -> (
                match behaviour0 with
                | Yielding_bool _ -> false
                | Yielding_int_like_compare_functions s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))))
            | _ -> false)
          | Standard_naked_immediate -> (
            match kind0 with
            | Standard_naked_immediate -> (
              match behaviour with
              | Yielding_bool c -> (
                match behaviour0 with
                | Yielding_bool c0 -> (
                  match c with
                  | Int_eq -> ( match c0 with Int_eq -> true | _ -> false)
                  | Int_neq -> ( match c0 with Int_neq -> true | _ -> false)
                  | Int_lt s -> (
                    match c0 with
                    | Int_lt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_gt s -> (
                    match c0 with
                    | Int_gt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_le s -> (
                    match c0 with
                    | Int_le s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_ge s -> (
                    match c0 with
                    | Int_ge s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false))
                | Yielding_int_like_compare_functions _ -> false)
              | Yielding_int_like_compare_functions s -> (
                match behaviour0 with
                | Yielding_bool _ -> false
                | Yielding_int_like_compare_functions s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))))
            | _ -> false)
          | Standard_naked_int8 -> (
            match kind0 with
            | Standard_naked_int8 -> (
              match behaviour with
              | Yielding_bool c -> (
                match behaviour0 with
                | Yielding_bool c0 -> (
                  match c with
                  | Int_eq -> ( match c0 with Int_eq -> true | _ -> false)
                  | Int_neq -> ( match c0 with Int_neq -> true | _ -> false)
                  | Int_lt s -> (
                    match c0 with
                    | Int_lt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_gt s -> (
                    match c0 with
                    | Int_gt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_le s -> (
                    match c0 with
                    | Int_le s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_ge s -> (
                    match c0 with
                    | Int_ge s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false))
                | Yielding_int_like_compare_functions _ -> false)
              | Yielding_int_like_compare_functions s -> (
                match behaviour0 with
                | Yielding_bool _ -> false
                | Yielding_int_like_compare_functions s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))))
            | _ -> false)
          | Standard_naked_int16 -> (
            match kind0 with
            | Standard_naked_int16 -> (
              match behaviour with
              | Yielding_bool c -> (
                match behaviour0 with
                | Yielding_bool c0 -> (
                  match c with
                  | Int_eq -> ( match c0 with Int_eq -> true | _ -> false)
                  | Int_neq -> ( match c0 with Int_neq -> true | _ -> false)
                  | Int_lt s -> (
                    match c0 with
                    | Int_lt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_gt s -> (
                    match c0 with
                    | Int_gt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_le s -> (
                    match c0 with
                    | Int_le s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_ge s -> (
                    match c0 with
                    | Int_ge s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false))
                | Yielding_int_like_compare_functions _ -> false)
              | Yielding_int_like_compare_functions s -> (
                match behaviour0 with
                | Yielding_bool _ -> false
                | Yielding_int_like_compare_functions s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))))
            | _ -> false)
          | Standard_naked_int32 -> (
            match kind0 with
            | Standard_naked_int32 -> (
              match behaviour with
              | Yielding_bool c -> (
                match behaviour0 with
                | Yielding_bool c0 -> (
                  match c with
                  | Int_eq -> ( match c0 with Int_eq -> true | _ -> false)
                  | Int_neq -> ( match c0 with Int_neq -> true | _ -> false)
                  | Int_lt s -> (
                    match c0 with
                    | Int_lt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_gt s -> (
                    match c0 with
                    | Int_gt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_le s -> (
                    match c0 with
                    | Int_le s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_ge s -> (
                    match c0 with
                    | Int_ge s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false))
                | Yielding_int_like_compare_functions _ -> false)
              | Yielding_int_like_compare_functions s -> (
                match behaviour0 with
                | Yielding_bool _ -> false
                | Yielding_int_like_compare_functions s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))))
            | _ -> false)
          | Standard_naked_int64 -> (
            match kind0 with
            | Standard_naked_int64 -> (
              match behaviour with
              | Yielding_bool c -> (
                match behaviour0 with
                | Yielding_bool c0 -> (
                  match c with
                  | Int_eq -> ( match c0 with Int_eq -> true | _ -> false)
                  | Int_neq -> ( match c0 with Int_neq -> true | _ -> false)
                  | Int_lt s -> (
                    match c0 with
                    | Int_lt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_gt s -> (
                    match c0 with
                    | Int_gt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_le s -> (
                    match c0 with
                    | Int_le s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_ge s -> (
                    match c0 with
                    | Int_ge s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false))
                | Yielding_int_like_compare_functions _ -> false)
              | Yielding_int_like_compare_functions s -> (
                match behaviour0 with
                | Yielding_bool _ -> false
                | Yielding_int_like_compare_functions s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))))
            | _ -> false)
          | Standard_naked_nativeint -> (
            match kind0 with
            | Standard_naked_nativeint -> (
              match behaviour with
              | Yielding_bool c -> (
                match behaviour0 with
                | Yielding_bool c0 -> (
                  match c with
                  | Int_eq -> ( match c0 with Int_eq -> true | _ -> false)
                  | Int_neq -> ( match c0 with Int_neq -> true | _ -> false)
                  | Int_lt s -> (
                    match c0 with
                    | Int_lt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_gt s -> (
                    match c0 with
                    | Int_gt s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_le s -> (
                    match c0 with
                    | Int_le s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false)
                  | Int_ge s -> (
                    match c0 with
                    | Int_ge s0 -> (
                      match s with
                      | Signed -> (
                        match s0 with Signed -> true | Unsigned -> false)
                      | Unsigned -> (
                        match s0 with Signed -> false | Unsigned -> true))
                    | _ -> false))
                | Yielding_int_like_compare_functions _ -> false)
              | Yielding_int_like_compare_functions s -> (
                match behaviour0 with
                | Yielding_bool _ -> false
                | Yielding_int_like_compare_functions s0 -> (
                  match s with
                  | Signed -> (
                    match s0 with Signed -> true | Unsigned -> false)
                  | Unsigned -> (
                    match s0 with Signed -> false | Unsigned -> true))))
            | _ -> false)))))

(** val prim_eqb : prim -> prim -> bool **)

let prim_eqb p p' = if prim_eq_dec p p' then true else false
