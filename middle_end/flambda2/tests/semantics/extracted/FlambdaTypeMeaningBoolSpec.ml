open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaCompareSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaSemanticsSpec
open FlambdaTypeGrammar
open FlambdaTypeMeaningSpec
open FlambdaValueSpec
open List
open ListDef
open PeanoNat

(** val lists_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec lists_eqb eqb0 l l' =
  match l with
  | [] -> ( match l' with [] -> true | _ :: _ -> false)
  | a :: l0 -> (
    match l' with
    | [] -> false
    | a' :: l'0 -> eqb0 a a' && lists_eqb eqb0 l0 l'0)

(** val value_eqb : value -> value -> bool **)

let rec value_eqb v v' =
  match v with
  | Value_const c -> (
    match v' with Value_const c' -> const_eqb c c' | _ -> false)
  | Value_closure (code, value_slots) -> (
    match v' with
    | Value_closure (code', value_slots') ->
      Pos.eqb code code'
      && lists_eqb
           (fun slot slot' ->
             Pos.eqb (fst slot) (fst slot') && value_eqb (snd slot) (snd slot'))
           value_slots value_slots'
    | _ -> false)
  | Value_closure_of_set (slot, function_decls, value_slots) -> (
    match v' with
    | Value_closure_of_set (slot', function_decls', value_slots') ->
      (Pos.eqb slot slot'
      && lists_eqb
           (fun decl decl' ->
             Pos.eqb (fst decl) (fst decl') && Pos.eqb (snd decl) (snd decl'))
           function_decls function_decls')
      && lists_eqb
           (fun slot0 slot'0 ->
             Pos.eqb (fst slot0) (fst slot'0)
             && value_eqb (snd slot0) (snd slot'0))
           value_slots value_slots'
    | _ -> false)
  | Value_symbol s -> (
    match v' with Value_symbol s' -> Pos.eqb s s' | _ -> false)
  | Value_block (tag, fields) -> (
    match v' with
    | Value_block (tag', fields') ->
      Z.eqb tag tag' && lists_eqb value_eqb fields fields'
    | _ -> false)
  | Value_boxed_number c -> (
    match v' with Value_boxed_number c' -> const_eqb c c' | _ -> false)

(** val is_poison_b : value -> bool **)

let is_poison_b = function
  | Value_const c -> ( match c with Poison _ -> true | _ -> false)
  | _ -> false

(** val is_tag_b : coq_Z -> bool **)

let is_tag_b n =
  Z.leb Z0 n
  && Z.leb n
       (Zpos
          (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))))

(** val relation_holds_b : static_env -> Relation.t -> value -> coq_Z -> bool **)

let relation_holds_b statics relation v n =
  match relation with
  | Relation.Is_null -> (
    match v with
    | Value_const c -> (
      match c with
      | Null -> Z.eqb n (Zpos Coq_xH)
      | _ -> kind_eqb (kind_of_value v) Value && Z.eqb n Z0)
    | _ -> kind_eqb (kind_of_value v) Value && Z.eqb n Z0)
  | Relation.Is_int -> (
    match v with
    | Value_const c -> (
      match c with
      | Tagged_immediate _ -> Z.eqb n (Zpos Coq_xH)
      | _ -> (
        match block_of statics v with Some _ -> Z.eqb n Z0 | None -> false))
    | _ -> (
      match block_of statics v with Some _ -> Z.eqb n Z0 | None -> false))
  | Relation.Get_tag -> (
    match v with
    | Value_const c -> (
      match c with
      | Tagged_immediate _ -> true
      | _ -> (
        match block_of statics v with
        | Some p ->
          let tag, _ = p in
          Z.eqb tag n && is_tag_b n
        | None -> false))
    | _ -> (
      match block_of statics v with
      | Some p ->
        let tag, _ = p in
        Z.eqb tag n && is_tag_b n
      | None -> false))

(** val block_has_shape_b : block_shape -> coq_Z -> value list -> bool **)

let block_has_shape_b shape tag fields =
  (match shape with
    | Scannable _ -> Z.ltb tag no_scan_tag
    | Float_record -> Z.eqb tag double_array_tag)
  && lists_eqb kind_eqb (map kind_of_value fields)
       (field_kinds shape (length fields))

(** val block_index_satisfied_b : coq_Z -> value list -> (nat, block_shape)
    row_like_index -> bool **)

let block_index_satisfied_b tag fields index =
  (match index.index_domain with
    | Row_like_index_domain.Known size -> Nat.eqb (length fields) size
    | Row_like_index_domain.At_least size -> Nat.leb size (length fields))
  && block_has_shape_b index.index_shape tag fields

(** val closures_index_satisfied_b : (function_slot * code_id) list ->
    (value_slot * value) list -> (set_of_closures_contents, unit) row_like_index
    -> bool **)

let closures_index_satisfied_b functions value_slots index =
  match index.index_domain with
  | Row_like_index_domain.Known contents ->
    Keyed.same_keys_b Pos.eqb contents.contents_closures (domain functions)
    && Keyed.same_keys_b Pos.eqb contents.contents_value_slots
         (domain value_slots)
  | Row_like_index_domain.At_least contents ->
    all_among contents.contents_closures (domain functions)
    && all_among contents.contents_value_slots (domain value_slots)

(** val variable_is_b : env -> variable option -> coq_Z -> bool **)

let variable_is_b vars x n =
  match x with
  | Some x0 -> (
    match lookup x0 vars with
    | Some v -> (
      match v with
      | Value_const c -> (
        match c with Naked_immediate i -> Z.eqb i n | _ -> false)
      | _ -> false)
    | None -> false)
  | None -> true

(** val descr_satisfied_b : env -> flambda_kind -> ('a1 -> bool) -> value -> 'a1
    type_descr -> bool **)

let descr_satisfied_b vars k head_satisfied_b v = function
  | Unknown -> kind_eqb (kind_of_value v) k
  | Ok a -> (
    match a with
    | No_alias head -> head_satisfied_b head
    | Equals s -> (
      match eval_simple vars s with
      | Some w -> value_eqb w v && kind_eqb (kind_of_value v) k
      | None -> false))
  | Bottom -> false

(** val head_of_kind_naked_immediate_satisfied_b : static_env -> env -> value ->
    head_of_kind_naked_immediate -> bool **)

let head_of_kind_naked_immediate_satisfied_b statics vars v head =
  match v with
  | Value_const c -> (
    match c with
    | Naked_immediate i ->
      (match head.naked_immediates with
        | Or_unknown.Known numbers -> Keyed.among Z.eqb i numbers
        | Or_unknown.Unknown -> true)
      && forallb
           (fun relation ->
             match value_of_name vars (snd relation) with
             | Some w -> relation_holds_b statics (fst relation) w i
             | None -> false)
           head.inverse_relations
    | _ -> false)
  | _ -> false

(** val naked_numbers_satisfied_b : naked_number_kind -> value -> coq_Z list ->
    bool **)

let naked_numbers_satisfied_b k v numbers =
  match v with
  | Value_const c -> (
    kind_eqb (kind_of_const c) (Naked_number k)
    &&
    match number_of_const c with
    | Some n -> Keyed.among Z.eqb n numbers
    | None -> false)
  | _ -> false

(** val fields_satisfied_b : (value -> flambda_type -> bool) -> flambda_type
    list -> value list -> bool **)

let rec fields_satisfied_b type_satisfied_b0 tys fields =
  match tys with
  | [] -> true
  | ty :: tys0 -> (
    match fields with
    | [] -> true
    | field :: fields0 ->
      type_satisfied_b0 field ty
      && fields_satisfied_b type_satisfied_b0 tys0 fields0)

(** val block_case_satisfied_b : (value -> flambda_type -> bool) ->
    (env_extension -> bool) -> coq_Z -> value list -> row_like_block_case ->
    bool **)

let block_case_satisfied_b type_satisfied_b0 env_extension_satisfied_b0 tag
    fields case =
  (block_index_satisfied_b tag fields case.case_index
  && fields_satisfied_b type_satisfied_b0 case.case_maps_to fields)
  && env_extension_satisfied_b0 case.case_env_extension

(** val closures_case_satisfied_b : (closures_entry -> bool) -> (env_extension
    -> bool) -> (function_slot * code_id) list -> (value_slot * value) list ->
    row_like_closures_case -> bool **)

let closures_case_satisfied_b closures_entry_satisfied_b0
    env_extension_satisfied_b0 functions value_slots case =
  (closures_index_satisfied_b functions value_slots case.case_index
  && closures_entry_satisfied_b0 case.case_maps_to)
  && env_extension_satisfied_b0 case.case_env_extension

(** val type_satisfied_b : static_env -> env -> value -> flambda_type -> bool **)

let type_satisfied_b statics vars =
  let rec type_satisfied_b0 v = function
    | Type_value ty ->
      descr_satisfied_b vars Value (head_of_kind_value_satisfied_b v) v ty
    | Type_naked_immediate ty ->
      descr_satisfied_b vars (Naked_number Kind_naked_immediate)
        (head_of_kind_naked_immediate_satisfied_b statics vars v)
        v ty
    | Type_naked_number (k, ty) ->
      descr_satisfied_b vars (Naked_number k)
        (naked_numbers_satisfied_b k v)
        v ty
    | Type_rec_info ty ->
      descr_satisfied_b vars Rec_info
        (fun _ -> kind_eqb (kind_of_value v) Rec_info)
        v ty
    | Type_region ty ->
      descr_satisfied_b vars Region
        (fun _ -> kind_eqb (kind_of_value v) Region)
        v ty
  and head_of_kind_value_satisfied_b v = function
    | Head_of_kind_value (non_null, is_null) -> (
      match v with
      | Value_const c -> (
        match c with
        | Null -> (
          match is_null with
          | Not_null -> false
          | Maybe_null is_null0 -> variable_is_b vars is_null0 (Zpos Coq_xH))
        | _ -> (
          (match non_null with
            | Unknown -> kind_eqb (kind_of_value v) Value
            | Ok head0 -> head_of_kind_value_non_null_satisfied_b v head0
            | Bottom -> false)
          &&
          match is_null with
          | Not_null -> true
          | Maybe_null is_null0 -> variable_is_b vars is_null0 Z0))
      | _ -> (
        (match non_null with
          | Unknown -> kind_eqb (kind_of_value v) Value
          | Ok head0 -> head_of_kind_value_non_null_satisfied_b v head0
          | Bottom -> false)
        &&
        match is_null with
        | Not_null -> true
        | Maybe_null is_null0 -> variable_is_b vars is_null0 Z0))
  and head_of_kind_value_non_null_satisfied_b v = function
    | Variant (is_int, immediates, get_tag, blocks, extensions, _) -> (
      match v with
      | Value_const c -> (
        match c with
        | Tagged_immediate i -> (
          (variable_is_b vars is_int (Zpos Coq_xH)
          &&
          match immediates with
          | Or_unknown.Known ty ->
            type_satisfied_b0 (Value_const (Naked_immediate i)) ty
          | Or_unknown.Unknown -> true)
          &&
          match extensions with
          | No_extensions -> true
          | Ext (when_immediate, _) -> env_extension_satisfied_b0 when_immediate
          )
        | _ -> (
          match block_of statics v with
          | Some p -> (
            let tag, fields = p in
            ((variable_is_b vars is_int Z0 && variable_is_b vars get_tag tag)
            &&
            match blocks with
            | Or_unknown.Known blocks0 ->
              row_like_for_blocks_satisfied_b tag fields blocks0
            | Or_unknown.Unknown -> true)
            &&
            match extensions with
            | No_extensions -> true
            | Ext (_, when_block) -> env_extension_satisfied_b0 when_block)
          | None -> false))
      | _ -> (
        match block_of statics v with
        | Some p -> (
          let tag, fields = p in
          ((variable_is_b vars is_int Z0 && variable_is_b vars get_tag tag)
          &&
          match blocks with
          | Or_unknown.Known blocks0 ->
            row_like_for_blocks_satisfied_b tag fields blocks0
          | Or_unknown.Unknown -> true)
          &&
          match extensions with
          | No_extensions -> true
          | Ext (_, when_block) -> env_extension_satisfied_b0 when_block)
        | None -> false))
    | Mutable_block _ -> false
    | Boxed_number (k, contents, _) -> (
      match boxed_number_of statics v with
      | Some c ->
        kind_eqb (kind_of_const c) (unboxed_kind k)
        && type_satisfied_b0 (Value_const c) contents
      | None -> false)
    | Closures (by_function_slot, _) -> (
      match closure_in_set statics v with
      | Some p ->
        let p0, value_slots = p in
        let slot, functions = p0 in
        row_like_for_closures_satisfied_b v slot functions value_slots
          by_function_slot
      | None -> false)
    | String strs -> (
      match string_of statics v with
      | Some bytes -> Keyed.among (lists_eqb Z.eqb) bytes strs
      | None -> false)
  and row_like_for_blocks_satisfied_b tag fields = function
    | Row_like_for_blocks (known_tags, other_tags, _) -> (
      Keyed.at_binding_b Z.eqb
        (fun case ->
          match case with
          | Or_unknown.Known case0 ->
            block_case_satisfied_b type_satisfied_b0 env_extension_satisfied_b0
              tag fields case0
          | Or_unknown.Unknown -> true)
        tag known_tags
      &&
      match Keyed.lookup Z.eqb tag known_tags with
      | Some _ -> true
      | None -> (
        match other_tags with
        | Or_bottom.Ok case ->
          block_case_satisfied_b type_satisfied_b0 env_extension_satisfied_b0
            tag fields case
        | Or_bottom.Bottom -> false))
  and row_like_for_closures_satisfied_b v slot functions value_slots = function
    | Row_like_for_closures known_closures ->
      is_bound slot known_closures
      && Keyed.at_binding_b Pos.eqb
           (closures_case_satisfied_b
              (closures_entry_satisfied_b0 v slot functions value_slots)
              env_extension_satisfied_b0 functions value_slots)
           slot known_closures
  and closures_entry_satisfied_b0 v slot functions value_slots = function
    | Closures_entry (function_types, closure_types, value_slot_types) ->
      (Keyed.for_all_bindings_b Pos.eqb
         (fun g function_type ->
           match function_type with
           | Or_unknown.Known function_type0 -> (
             match lookup g functions with
             | Some code -> Pos.eqb code function_type0.function_type_code_id
             | None -> true)
           | Or_unknown.Unknown -> true)
         function_types
      && Keyed.for_all_bindings_b Pos.eqb
           (fun g ty ->
             match project_function_slot statics slot g v with
             | Some closure -> type_satisfied_b0 closure ty
             | None -> true)
           closure_types)
      && Keyed.for_all_bindings_b Pos.eqb
           (fun w ty ->
             match lookup w value_slots with
             | Some contents -> type_satisfied_b0 contents ty
             | None -> true)
           value_slot_types
  and env_extension_satisfied_b0 = function
    | Env_extension equations ->
      Keyed.for_all_bindings_b name_eqb
        (fun n ty ->
          match value_of_name vars n with
          | Some v -> type_satisfied_b0 v ty
          | None -> false)
        equations
  in
  type_satisfied_b0

(** val closures_entry_satisfied_b : static_env -> env -> value -> function_slot
    -> (function_slot * code_id) list -> (value_slot * value) list ->
    closures_entry -> bool **)

let closures_entry_satisfied_b statics vars =
  let rec type_satisfied_b0 v = function
    | Type_value ty ->
      descr_satisfied_b vars Value (head_of_kind_value_satisfied_b v) v ty
    | Type_naked_immediate ty ->
      descr_satisfied_b vars (Naked_number Kind_naked_immediate)
        (head_of_kind_naked_immediate_satisfied_b statics vars v)
        v ty
    | Type_naked_number (k, ty) ->
      descr_satisfied_b vars (Naked_number k)
        (naked_numbers_satisfied_b k v)
        v ty
    | Type_rec_info ty ->
      descr_satisfied_b vars Rec_info
        (fun _ -> kind_eqb (kind_of_value v) Rec_info)
        v ty
    | Type_region ty ->
      descr_satisfied_b vars Region
        (fun _ -> kind_eqb (kind_of_value v) Region)
        v ty
  and head_of_kind_value_satisfied_b v = function
    | Head_of_kind_value (non_null, is_null) -> (
      match v with
      | Value_const c -> (
        match c with
        | Null -> (
          match is_null with
          | Not_null -> false
          | Maybe_null is_null0 -> variable_is_b vars is_null0 (Zpos Coq_xH))
        | _ -> (
          (match non_null with
            | Unknown -> kind_eqb (kind_of_value v) Value
            | Ok head0 -> head_of_kind_value_non_null_satisfied_b v head0
            | Bottom -> false)
          &&
          match is_null with
          | Not_null -> true
          | Maybe_null is_null0 -> variable_is_b vars is_null0 Z0))
      | _ -> (
        (match non_null with
          | Unknown -> kind_eqb (kind_of_value v) Value
          | Ok head0 -> head_of_kind_value_non_null_satisfied_b v head0
          | Bottom -> false)
        &&
        match is_null with
        | Not_null -> true
        | Maybe_null is_null0 -> variable_is_b vars is_null0 Z0))
  and head_of_kind_value_non_null_satisfied_b v = function
    | Variant (is_int, immediates, get_tag, blocks, extensions, _) -> (
      match v with
      | Value_const c -> (
        match c with
        | Tagged_immediate i -> (
          (variable_is_b vars is_int (Zpos Coq_xH)
          &&
          match immediates with
          | Or_unknown.Known ty ->
            type_satisfied_b0 (Value_const (Naked_immediate i)) ty
          | Or_unknown.Unknown -> true)
          &&
          match extensions with
          | No_extensions -> true
          | Ext (when_immediate, _) -> env_extension_satisfied_b0 when_immediate
          )
        | _ -> (
          match block_of statics v with
          | Some p -> (
            let tag, fields = p in
            ((variable_is_b vars is_int Z0 && variable_is_b vars get_tag tag)
            &&
            match blocks with
            | Or_unknown.Known blocks0 ->
              row_like_for_blocks_satisfied_b tag fields blocks0
            | Or_unknown.Unknown -> true)
            &&
            match extensions with
            | No_extensions -> true
            | Ext (_, when_block) -> env_extension_satisfied_b0 when_block)
          | None -> false))
      | _ -> (
        match block_of statics v with
        | Some p -> (
          let tag, fields = p in
          ((variable_is_b vars is_int Z0 && variable_is_b vars get_tag tag)
          &&
          match blocks with
          | Or_unknown.Known blocks0 ->
            row_like_for_blocks_satisfied_b tag fields blocks0
          | Or_unknown.Unknown -> true)
          &&
          match extensions with
          | No_extensions -> true
          | Ext (_, when_block) -> env_extension_satisfied_b0 when_block)
        | None -> false))
    | Mutable_block _ -> false
    | Boxed_number (k, contents, _) -> (
      match boxed_number_of statics v with
      | Some c ->
        kind_eqb (kind_of_const c) (unboxed_kind k)
        && type_satisfied_b0 (Value_const c) contents
      | None -> false)
    | Closures (by_function_slot, _) -> (
      match closure_in_set statics v with
      | Some p ->
        let p0, value_slots = p in
        let slot, functions = p0 in
        row_like_for_closures_satisfied_b v slot functions value_slots
          by_function_slot
      | None -> false)
    | String strs -> (
      match string_of statics v with
      | Some bytes -> Keyed.among (lists_eqb Z.eqb) bytes strs
      | None -> false)
  and row_like_for_blocks_satisfied_b tag fields = function
    | Row_like_for_blocks (known_tags, other_tags, _) -> (
      Keyed.at_binding_b Z.eqb
        (fun case ->
          match case with
          | Or_unknown.Known case0 ->
            block_case_satisfied_b type_satisfied_b0 env_extension_satisfied_b0
              tag fields case0
          | Or_unknown.Unknown -> true)
        tag known_tags
      &&
      match Keyed.lookup Z.eqb tag known_tags with
      | Some _ -> true
      | None -> (
        match other_tags with
        | Or_bottom.Ok case ->
          block_case_satisfied_b type_satisfied_b0 env_extension_satisfied_b0
            tag fields case
        | Or_bottom.Bottom -> false))
  and row_like_for_closures_satisfied_b v slot functions value_slots = function
    | Row_like_for_closures known_closures ->
      is_bound slot known_closures
      && Keyed.at_binding_b Pos.eqb
           (closures_case_satisfied_b
              (closures_entry_satisfied_b0 v slot functions value_slots)
              env_extension_satisfied_b0 functions value_slots)
           slot known_closures
  and closures_entry_satisfied_b0 v slot functions value_slots = function
    | Closures_entry (function_types, closure_types, value_slot_types) ->
      (Keyed.for_all_bindings_b Pos.eqb
         (fun g function_type ->
           match function_type with
           | Or_unknown.Known function_type0 -> (
             match lookup g functions with
             | Some code -> Pos.eqb code function_type0.function_type_code_id
             | None -> true)
           | Or_unknown.Unknown -> true)
         function_types
      && Keyed.for_all_bindings_b Pos.eqb
           (fun g ty ->
             match project_function_slot statics slot g v with
             | Some closure -> type_satisfied_b0 closure ty
             | None -> true)
           closure_types)
      && Keyed.for_all_bindings_b Pos.eqb
           (fun w ty ->
             match lookup w value_slots with
             | Some contents -> type_satisfied_b0 contents ty
             | None -> true)
           value_slot_types
  and env_extension_satisfied_b0 = function
    | Env_extension equations ->
      Keyed.for_all_bindings_b name_eqb
        (fun n ty ->
          match value_of_name vars n with
          | Some v -> type_satisfied_b0 v ty
          | None -> false)
        equations
  in
  closures_entry_satisfied_b0

(** val env_extension_satisfied_b : static_env -> env -> env_extension -> bool **)

let env_extension_satisfied_b statics vars =
  let rec type_satisfied_b0 v = function
    | Type_value ty ->
      descr_satisfied_b vars Value (head_of_kind_value_satisfied_b v) v ty
    | Type_naked_immediate ty ->
      descr_satisfied_b vars (Naked_number Kind_naked_immediate)
        (head_of_kind_naked_immediate_satisfied_b statics vars v)
        v ty
    | Type_naked_number (k, ty) ->
      descr_satisfied_b vars (Naked_number k)
        (naked_numbers_satisfied_b k v)
        v ty
    | Type_rec_info ty ->
      descr_satisfied_b vars Rec_info
        (fun _ -> kind_eqb (kind_of_value v) Rec_info)
        v ty
    | Type_region ty ->
      descr_satisfied_b vars Region
        (fun _ -> kind_eqb (kind_of_value v) Region)
        v ty
  and head_of_kind_value_satisfied_b v = function
    | Head_of_kind_value (non_null, is_null) -> (
      match v with
      | Value_const c -> (
        match c with
        | Null -> (
          match is_null with
          | Not_null -> false
          | Maybe_null is_null0 -> variable_is_b vars is_null0 (Zpos Coq_xH))
        | _ -> (
          (match non_null with
            | Unknown -> kind_eqb (kind_of_value v) Value
            | Ok head0 -> head_of_kind_value_non_null_satisfied_b v head0
            | Bottom -> false)
          &&
          match is_null with
          | Not_null -> true
          | Maybe_null is_null0 -> variable_is_b vars is_null0 Z0))
      | _ -> (
        (match non_null with
          | Unknown -> kind_eqb (kind_of_value v) Value
          | Ok head0 -> head_of_kind_value_non_null_satisfied_b v head0
          | Bottom -> false)
        &&
        match is_null with
        | Not_null -> true
        | Maybe_null is_null0 -> variable_is_b vars is_null0 Z0))
  and head_of_kind_value_non_null_satisfied_b v = function
    | Variant (is_int, immediates, get_tag, blocks, extensions, _) -> (
      match v with
      | Value_const c -> (
        match c with
        | Tagged_immediate i -> (
          (variable_is_b vars is_int (Zpos Coq_xH)
          &&
          match immediates with
          | Or_unknown.Known ty ->
            type_satisfied_b0 (Value_const (Naked_immediate i)) ty
          | Or_unknown.Unknown -> true)
          &&
          match extensions with
          | No_extensions -> true
          | Ext (when_immediate, _) -> env_extension_satisfied_b0 when_immediate
          )
        | _ -> (
          match block_of statics v with
          | Some p -> (
            let tag, fields = p in
            ((variable_is_b vars is_int Z0 && variable_is_b vars get_tag tag)
            &&
            match blocks with
            | Or_unknown.Known blocks0 ->
              row_like_for_blocks_satisfied_b tag fields blocks0
            | Or_unknown.Unknown -> true)
            &&
            match extensions with
            | No_extensions -> true
            | Ext (_, when_block) -> env_extension_satisfied_b0 when_block)
          | None -> false))
      | _ -> (
        match block_of statics v with
        | Some p -> (
          let tag, fields = p in
          ((variable_is_b vars is_int Z0 && variable_is_b vars get_tag tag)
          &&
          match blocks with
          | Or_unknown.Known blocks0 ->
            row_like_for_blocks_satisfied_b tag fields blocks0
          | Or_unknown.Unknown -> true)
          &&
          match extensions with
          | No_extensions -> true
          | Ext (_, when_block) -> env_extension_satisfied_b0 when_block)
        | None -> false))
    | Mutable_block _ -> false
    | Boxed_number (k, contents, _) -> (
      match boxed_number_of statics v with
      | Some c ->
        kind_eqb (kind_of_const c) (unboxed_kind k)
        && type_satisfied_b0 (Value_const c) contents
      | None -> false)
    | Closures (by_function_slot, _) -> (
      match closure_in_set statics v with
      | Some p ->
        let p0, value_slots = p in
        let slot, functions = p0 in
        row_like_for_closures_satisfied_b v slot functions value_slots
          by_function_slot
      | None -> false)
    | String strs -> (
      match string_of statics v with
      | Some bytes -> Keyed.among (lists_eqb Z.eqb) bytes strs
      | None -> false)
  and row_like_for_blocks_satisfied_b tag fields = function
    | Row_like_for_blocks (known_tags, other_tags, _) -> (
      Keyed.at_binding_b Z.eqb
        (fun case ->
          match case with
          | Or_unknown.Known case0 ->
            block_case_satisfied_b type_satisfied_b0 env_extension_satisfied_b0
              tag fields case0
          | Or_unknown.Unknown -> true)
        tag known_tags
      &&
      match Keyed.lookup Z.eqb tag known_tags with
      | Some _ -> true
      | None -> (
        match other_tags with
        | Or_bottom.Ok case ->
          block_case_satisfied_b type_satisfied_b0 env_extension_satisfied_b0
            tag fields case
        | Or_bottom.Bottom -> false))
  and row_like_for_closures_satisfied_b v slot functions value_slots = function
    | Row_like_for_closures known_closures ->
      is_bound slot known_closures
      && Keyed.at_binding_b Pos.eqb
           (closures_case_satisfied_b
              (closures_entry_satisfied_b0 v slot functions value_slots)
              env_extension_satisfied_b0 functions value_slots)
           slot known_closures
  and closures_entry_satisfied_b0 v slot functions value_slots = function
    | Closures_entry (function_types, closure_types, value_slot_types) ->
      (Keyed.for_all_bindings_b Pos.eqb
         (fun g function_type ->
           match function_type with
           | Or_unknown.Known function_type0 -> (
             match lookup g functions with
             | Some code -> Pos.eqb code function_type0.function_type_code_id
             | None -> true)
           | Or_unknown.Unknown -> true)
         function_types
      && Keyed.for_all_bindings_b Pos.eqb
           (fun g ty ->
             match project_function_slot statics slot g v with
             | Some closure -> type_satisfied_b0 closure ty
             | None -> true)
           closure_types)
      && Keyed.for_all_bindings_b Pos.eqb
           (fun w ty ->
             match lookup w value_slots with
             | Some contents -> type_satisfied_b0 contents ty
             | None -> true)
           value_slot_types
  and env_extension_satisfied_b0 = function
    | Env_extension equations ->
      Keyed.for_all_bindings_b name_eqb
        (fun n ty ->
          match value_of_name vars n with
          | Some v -> type_satisfied_b0 v ty
          | None -> false)
        equations
  in
  env_extension_satisfied_b0

(** val row_like_block_case_satisfied_b : static_env -> env -> coq_Z -> value
    list -> row_like_block_case -> bool **)

let row_like_block_case_satisfied_b statics vars tag fields case =
  block_case_satisfied_b
    (type_satisfied_b statics vars)
    (env_extension_satisfied_b statics vars)
    tag fields case

(** val row_like_closures_case_satisfied_b : static_env -> env -> value ->
    function_slot -> (function_slot * code_id) list -> (value_slot * value) list
    -> row_like_closures_case -> bool **)

let row_like_closures_case_satisfied_b statics vars v slot functions value_slots
    case =
  closures_case_satisfied_b
    (closures_entry_satisfied_b statics vars v slot functions value_slots)
    (env_extension_satisfied_b statics vars)
    functions value_slots case
