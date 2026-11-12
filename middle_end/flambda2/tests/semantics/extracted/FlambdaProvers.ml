open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBindingTime
open FlambdaCompareSpec
open FlambdaExpandHead
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeAccessSpec
open FlambdaTypeEqualSpec
open FlambdaTypeGrammar
open FlambdaTypeMeaningBoolSpec
open FlambdaTypingEnv
open List
open PeanoNat

type descr_oub =
  | Oub_value of head_of_kind_value or_unknown_or_bottom
  | Oub_naked_immediate of head_of_kind_naked_immediate or_unknown_or_bottom
  | Oub_naked_number of naked_number_kind * coq_Z list or_unknown_or_bottom
  | Oub_rec_info of unit or_unknown_or_bottom
  | Oub_region of unit or_unknown_or_bottom

(** val descr_oub_of_expanded : Expanded_type.t -> descr_oub **)

let descr_oub_of_expanded expanded =
  match expanded.Expanded_type.descr with
  | Unknown -> (
    match expanded.Expanded_type.kind with
    | Value -> Oub_value Unknown
    | Naked_number k -> (
      match k with
      | Kind_naked_immediate -> Oub_naked_immediate Unknown
      | _ -> Oub_naked_number (k, Unknown))
    | Region -> Oub_region Unknown
    | Rec_info -> Oub_rec_info Unknown)
  | Ok a -> (
    match a with
    | Expanded_type.Head_value head -> Oub_value (Ok head)
    | Expanded_type.Head_naked_immediate head -> Oub_naked_immediate (Ok head)
    | Expanded_type.Head_naked_number (k, head) -> Oub_naked_number (k, Ok head)
    | Expanded_type.Head_rec_info head -> Oub_rec_info (Ok head)
    | Expanded_type.Head_region head -> Oub_region (Ok head))
  | Bottom -> (
    match expanded.Expanded_type.kind with
    | Value -> Oub_value Bottom
    | Naked_number k -> (
      match k with
      | Kind_naked_immediate -> Oub_naked_immediate Bottom
      | _ -> Oub_naked_number (k, Bottom))
    | Region -> Oub_region Bottom
    | Rec_info -> Oub_rec_info Bottom)

module Meet_shortcut = struct
  type 'a t =
    | Known_result of 'a
    | Need_meet
    | Invalid
end

module Proof_of_property = struct
  type 'a t =
    | Proved of 'a
    | Unknown
end

module Generic_proof = struct
  type 'a t =
    | Proved of 'a
    | Unknown
    | Invalid
end

module Provers = struct
  (** val is_bottom : Typing_env.t -> flambda_type -> bool option **)

  let is_bottom tenv t0 =
    match expand_head tenv t0 with
    | Some expanded -> Some (Expanded_type.is_bottom expanded)
    | None -> None

  (** val expand_head : Typing_env.t -> flambda_type -> descr_oub option **)

  let expand_head tenv t0 =
    match expand_head tenv t0 with
    | Some expanded -> Some (descr_oub_of_expanded expanded)
    | None -> None

  (** val wrong_kind : 'a1 -> 'a1 **)

  let wrong_kind default = default

  (** val as_meet_shortcut : 'a1 Generic_proof.t -> 'a1 Meet_shortcut.t **)

  let as_meet_shortcut = function
    | Generic_proof.Proved x -> Meet_shortcut.Known_result x
    | Generic_proof.Unknown -> Meet_shortcut.Need_meet
    | Generic_proof.Invalid -> Meet_shortcut.Invalid

  (** val as_property : 'a1 Generic_proof.t -> 'a1 Proof_of_property.t **)

  let as_property = function
    | Generic_proof.Proved x -> Proof_of_property.Proved x
    | _ -> Proof_of_property.Unknown

  (** val gen_value_to_gen : (Typing_env.t -> head_of_kind_value_non_null -> 'a1
      Generic_proof.t option) -> Typing_env.t -> flambda_type -> 'a1
      Generic_proof.t option **)

  let gen_value_to_gen prove_gen tenv t0 =
    match expand_head tenv t0 with
    | Some expanded -> (
      match expanded with
      | Oub_value head0 -> (
        match head0 with
        | Unknown -> Some Generic_proof.Unknown
        | Ok a -> (
          let (Head_of_kind_value (non_null, is_null)) = a in
          match non_null with
          | Unknown -> Some Generic_proof.Unknown
          | Ok head -> (
            match is_null with
            | Not_null -> prove_gen tenv head
            | Maybe_null _ -> Some Generic_proof.Unknown)
          | Bottom -> (
            match is_null with
            | Not_null -> Some Generic_proof.Invalid
            | Maybe_null _ -> Some Generic_proof.Unknown))
        | Bottom -> Some Generic_proof.Invalid)
      | _ -> Some (wrong_kind Generic_proof.Invalid))
    | None -> None

  (** val gen_value_to_proof : (Typing_env.t -> head_of_kind_value_non_null ->
      'a1 Generic_proof.t option) -> Typing_env.t -> flambda_type -> 'a1
      Proof_of_property.t option **)

  let gen_value_to_proof prove_gen tenv t0 =
    match expand_head tenv t0 with
    | Some expanded -> (
      match expanded with
      | Oub_value head0 -> (
        match head0 with
        | Ok a -> (
          let (Head_of_kind_value (non_null, is_null)) = a in
          match non_null with
          | Ok head -> (
            match is_null with
            | Not_null -> (
              match prove_gen tenv head with
              | Some proof -> Some (as_property proof)
              | None -> None)
            | Maybe_null _ -> Some Proof_of_property.Unknown)
          | _ -> Some Proof_of_property.Unknown)
        | _ -> Some Proof_of_property.Unknown)
      | _ -> Some (wrong_kind Proof_of_property.Unknown))
    | None -> None

  (** val gen_value_to_meet : (Typing_env.t -> head_of_kind_value_non_null ->
      'a1 Generic_proof.t option) -> Typing_env.t -> flambda_type -> 'a1
      Meet_shortcut.t option **)

  let gen_value_to_meet prove_gen tenv t0 =
    match expand_head tenv t0 with
    | Some expanded -> (
      match expanded with
      | Oub_value head0 -> (
        match head0 with
        | Unknown -> Some Meet_shortcut.Need_meet
        | Ok a -> (
          let (Head_of_kind_value (non_null, _)) = a in
          match non_null with
          | Unknown -> Some Meet_shortcut.Need_meet
          | Ok head -> (
            match prove_gen tenv head with
            | Some proof -> Some (as_meet_shortcut proof)
            | None -> None)
          | Bottom -> Some Meet_shortcut.Invalid)
        | Bottom -> Some Meet_shortcut.Invalid)
      | _ -> Some (wrong_kind Meet_shortcut.Invalid))
    | None -> None

  (** val prove_is_int_generic_value : bool -> Typing_env.t ->
      head_of_kind_value_non_null -> bool Generic_proof.t option **)

  let prove_is_int_generic_value variant_only tenv = function
    | Variant (_, immediates, _, blocks, _, _) -> (
      match blocks with
      | Or_unknown.Known blocks0 -> (
        match immediates with
        | Or_unknown.Known imms -> (
          if row_like_for_blocks_is_bottom blocks0
          then
            match is_bottom tenv imms with
            | Some imms_bottom ->
              if imms_bottom
              then Some Generic_proof.Invalid
              else Some (Generic_proof.Proved true)
            | None -> None
          else
            match is_bottom tenv imms with
            | Some imms_bottom ->
              if imms_bottom
              then Some (Generic_proof.Proved false)
              else Some Generic_proof.Unknown
            | None -> None)
        | Or_unknown.Unknown ->
          if row_like_for_blocks_is_bottom blocks0
          then Some (Generic_proof.Proved true)
          else Some Generic_proof.Unknown)
      | Or_unknown.Unknown -> (
        match immediates with
        | Or_unknown.Known imms -> (
          match is_bottom tenv imms with
          | Some imms_bottom ->
            if imms_bottom
            then Some (Generic_proof.Proved false)
            else Some Generic_proof.Unknown
          | None -> None)
        | Or_unknown.Unknown -> Some Generic_proof.Unknown))
    | Mutable_block _ -> Some (Generic_proof.Proved false)
    | _ ->
      if variant_only
      then Some Generic_proof.Invalid
      else Some (Generic_proof.Proved false)

  (** val prove_is_int_generic : bool -> Typing_env.t -> flambda_type -> bool
      Generic_proof.t option **)

  let prove_is_int_generic variant_only tenv t0 =
    gen_value_to_gen (prove_is_int_generic_value variant_only) tenv t0

  (** val prove_is_int : Typing_env.t -> flambda_type -> bool
      Proof_of_property.t option **)

  let prove_is_int tenv t0 =
    gen_value_to_proof (prove_is_int_generic_value false) tenv t0

  (** val meet_is_int_variant_only : Typing_env.t -> flambda_type -> bool
      Meet_shortcut.t option **)

  let meet_is_int_variant_only tenv t0 =
    gen_value_to_meet (prove_is_int_generic_value true) tenv t0

  (** val prove_get_tag_generic_value : Typing_env.t ->
      head_of_kind_value_non_null -> coq_Z list Generic_proof.t option **)

  let prove_get_tag_generic_value tenv = function
    | Variant (_, immediates, _, blocks, _, _) -> (
      match immediates with
      | Or_unknown.Known imms -> (
        match is_bottom tenv imms with
        | Some imms_bottom -> (
          if negb imms_bottom
          then Some Generic_proof.Unknown
          else
            match blocks with
            | Or_unknown.Known blocks0 -> (
              match row_like_for_blocks_all_tags blocks0 with
              | Or_unknown.Known tags ->
                if Keyed.is_empty tags
                then Some Generic_proof.Invalid
                else Some (Generic_proof.Proved tags)
              | Or_unknown.Unknown -> Some Generic_proof.Unknown)
            | Or_unknown.Unknown -> Some Generic_proof.Unknown)
        | None -> None)
      | Or_unknown.Unknown -> Some Generic_proof.Unknown)
    | _ -> Some Generic_proof.Unknown

  (** val prove_get_tag_generic : Typing_env.t -> flambda_type -> coq_Z list
      Generic_proof.t option **)

  let prove_get_tag_generic tenv t0 =
    gen_value_to_gen prove_get_tag_generic_value tenv t0

  (** val prove_get_tag : Typing_env.t -> flambda_type -> coq_Z list
      Proof_of_property.t option **)

  let prove_get_tag tenv t0 =
    gen_value_to_proof prove_get_tag_generic_value tenv t0

  (** val prove_is_null_generic : Typing_env.t -> flambda_type -> bool
      Generic_proof.t option **)

  let prove_is_null_generic tenv t0 =
    match expand_head tenv t0 with
    | Some expanded -> (
      match expanded with
      | Oub_value head -> (
        match head with
        | Unknown -> Some Generic_proof.Unknown
        | Ok a -> (
          let (Head_of_kind_value (non_null, is_null)) = a in
          match non_null with
          | Bottom -> (
            match is_null with
            | Not_null -> Some Generic_proof.Invalid
            | Maybe_null _ -> Some (Generic_proof.Proved true))
          | _ -> (
            match is_null with
            | Not_null -> Some (Generic_proof.Proved false)
            | Maybe_null _ -> Some Generic_proof.Unknown))
        | Bottom -> Some Generic_proof.Invalid)
      | _ -> Some (wrong_kind Generic_proof.Invalid))
    | None -> None

  (** val meet_is_null : Typing_env.t -> flambda_type -> bool Meet_shortcut.t
      option **)

  let meet_is_null tenv t0 =
    match prove_is_null_generic tenv t0 with
    | Some proof -> Some (as_meet_shortcut proof)
    | None -> None

  (** val these_immediates : coq_Z list -> coq_Z list Generic_proof.t **)

  let these_immediates imms =
    if Keyed.is_empty imms
    then Generic_proof.Invalid
    else Generic_proof.Proved imms

  (** val meet_these_immediates : coq_Z list -> coq_Z list Generic_proof.t ->
      coq_Z list Generic_proof.t **)

  let meet_these_immediates imms = function
    | Generic_proof.Proved imms' ->
      these_immediates (Keyed.inter Z.eqb imms imms')
    | Generic_proof.Unknown -> these_immediates imms
    | Generic_proof.Invalid -> Generic_proof.Invalid

  (** val meet_this_immediate : coq_Z -> coq_Z list Generic_proof.t -> coq_Z
      list Generic_proof.t **)

  let meet_this_immediate imm proof = meet_these_immediates (imm :: []) proof

  (** val prove_naked_immediates_relation : Typing_env.t -> Relation.t -> name
      -> coq_Z list Generic_proof.t -> coq_Z list Generic_proof.t option **)

  let prove_naked_immediates_relation tenv relation name0 imms =
    let ty = alias_type_of Value (simple_of_name name0) in
    match relation with
    | Relation.Is_null -> (
      match prove_is_null_generic tenv ty with
      | Some proof -> (
        match proof with
        | Generic_proof.Proved b -> Some (meet_this_immediate (Z.b2z b) imms)
        | Generic_proof.Unknown -> Some imms
        | Generic_proof.Invalid -> Some Generic_proof.Invalid)
      | None -> None)
    | Relation.Is_int -> (
      match prove_is_int_generic true tenv ty with
      | Some proof -> (
        match proof with
        | Generic_proof.Proved b -> Some (meet_this_immediate (Z.b2z b) imms)
        | Generic_proof.Unknown -> Some imms
        | Generic_proof.Invalid -> Some Generic_proof.Invalid)
      | None -> None)
    | Relation.Get_tag -> (
      match prove_get_tag_generic tenv ty with
      | Some proof -> (
        match proof with
        | Generic_proof.Proved tags -> Some (meet_these_immediates tags imms)
        | Generic_proof.Unknown -> Some imms
        | Generic_proof.Invalid -> Some Generic_proof.Invalid)
      | None -> None)

  (** val prove_naked_immediates_generic : Typing_env.t -> flambda_type -> coq_Z
      list Generic_proof.t option **)

  let prove_naked_immediates_generic tenv t0 =
    match expand_head tenv t0 with
    | Some expanded -> (
      match expanded with
      | Oub_naked_immediate head0 -> (
        match head0 with
        | Unknown -> Some Generic_proof.Unknown
        | Ok head ->
          let proof =
            match head.naked_immediates with
            | Or_unknown.Known imms -> these_immediates imms
            | Or_unknown.Unknown -> Generic_proof.Unknown
          in
          fold_left
            (fun imms relation_and_name ->
              match imms with
              | Some imms0 ->
                prove_naked_immediates_relation tenv (fst relation_and_name)
                  (snd relation_and_name) imms0
              | None -> None)
            head.inverse_relations (Some proof)
        | Bottom -> Some Generic_proof.Invalid)
      | _ -> Some (wrong_kind Generic_proof.Invalid))
    | None -> None

  (** val meet_naked_immediates : Typing_env.t -> flambda_type -> coq_Z list
      Meet_shortcut.t option **)

  let meet_naked_immediates tenv t0 =
    match prove_naked_immediates_generic tenv t0 with
    | Some proof -> Some (as_meet_shortcut proof)
    | None -> None

  (** val meet_equals_tagged_immediates_value : Typing_env.t ->
      head_of_kind_value_non_null -> coq_Z list Generic_proof.t option **)

  let meet_equals_tagged_immediates_value tenv = function
    | Variant (_, immediates, _, _, _, _) -> (
      match immediates with
      | Or_unknown.Known imms -> prove_naked_immediates_generic tenv imms
      | Or_unknown.Unknown -> Some Generic_proof.Unknown)
    | _ -> Some Generic_proof.Invalid

  (** val meet_equals_tagged_immediates : Typing_env.t -> flambda_type -> coq_Z
      list Meet_shortcut.t option **)

  let meet_equals_tagged_immediates tenv t0 =
    gen_value_to_meet meet_equals_tagged_immediates_value tenv t0

  (** val canonical_simple_of_alias : Typing_env.t -> Name_mode.t ->
      flambda_type -> simple option option **)

  let canonical_simple_of_alias tenv min_name_mode t0 =
    match get_alias_opt t0 with
    | Some simple0 ->
      Typing_env.get_canonical_simple_exn tenv (Some min_name_mode) None simple0
    | None -> Some None

  type tagging_proof_kind =
    | Prove
    | Meet

  (** val inspect_tagging_immediates : Name_mode.t -> Typing_env.t ->
      flambda_type Or_unknown.t -> simple Generic_proof.t option **)

  let inspect_tagging_immediates min_name_mode tenv = function
    | Or_unknown.Known t0 -> (
      match canonical_simple_of_alias tenv min_name_mode t0 with
      | Some from_alias -> (
        match from_alias with
        | Some simple0 -> Some (Generic_proof.Proved simple0)
        | None -> (
          match meet_naked_immediates tenv t0 with
          | Some shortcut -> (
            match shortcut with
            | Meet_shortcut.Known_result imms -> (
              match Keyed.get_singleton Z.eqb imms with
              | Some imm ->
                Some (Generic_proof.Proved (Const (Naked_immediate imm)))
              | None -> Some Generic_proof.Unknown)
            | Meet_shortcut.Need_meet -> Some Generic_proof.Unknown
            | Meet_shortcut.Invalid -> Some Generic_proof.Invalid)
          | None -> None))
      | None -> None)
    | Or_unknown.Unknown -> Some Generic_proof.Unknown

  (** val inspect_tagging_of_simple_value : tagging_proof_kind -> Name_mode.t ->
      Typing_env.t -> head_of_kind_value_non_null -> simple Generic_proof.t
      option **)

  let inspect_tagging_of_simple_value proof_kind min_name_mode tenv = function
    | Variant (_, immediates, _, blocks, _, _) -> (
      match proof_kind with
      | Prove -> (
        match blocks with
        | Or_unknown.Known blocks0 ->
          if row_like_for_blocks_is_bottom blocks0
          then inspect_tagging_immediates min_name_mode tenv immediates
          else Some Generic_proof.Unknown
        | Or_unknown.Unknown -> Some Generic_proof.Unknown)
      | Meet -> inspect_tagging_immediates min_name_mode tenv immediates)
    | _ -> Some Generic_proof.Unknown

  (** val meet_tagging_of_simple : Typing_env.t -> Name_mode.t -> flambda_type
      -> simple Meet_shortcut.t option **)

  let meet_tagging_of_simple tenv min_name_mode t0 =
    gen_value_to_meet
      (inspect_tagging_of_simple_value Meet min_name_mode)
      tenv t0

  (** val meet_boxed_number_containing_simple : boxable_number -> Typing_env.t
      -> Name_mode.t -> flambda_type -> simple Meet_shortcut.t option **)

  let meet_boxed_number_containing_simple kind0 tenv min_name_mode t0 =
    let contents_of_boxed_number =
     fun ty_value ->
      match ty_value with
      | Variant (_, _, _, _, _, _) -> None
      | Mutable_block _ -> None
      | Boxed_number (k, ty, _) ->
        if boxable_number_eqb k kind0 then Some ty else None
      | _ -> None
    in
    match expand_head tenv t0 with
    | Some expanded -> (
      match expanded with
      | Oub_value head -> (
        match head with
        | Unknown -> Some Meet_shortcut.Need_meet
        | Ok a -> (
          let (Head_of_kind_value (non_null, _)) = a in
          match non_null with
          | Unknown -> Some Meet_shortcut.Need_meet
          | Ok ty_value -> (
            match contents_of_boxed_number ty_value with
            | Some ty -> (
              match canonical_simple_of_alias tenv min_name_mode ty with
              | Some canonical -> (
                match canonical with
                | Some simple0 -> Some (Meet_shortcut.Known_result simple0)
                | None -> Some Meet_shortcut.Need_meet)
              | None -> None)
            | None -> Some Meet_shortcut.Invalid)
          | Bottom -> Some Meet_shortcut.Invalid)
        | Bottom -> Some Meet_shortcut.Invalid)
      | _ -> Some (wrong_kind Meet_shortcut.Invalid))
    | None -> None

  (** val meet_block_field_simple_value : Name_mode.t -> flambda_kind -> nat ->
      Typing_env.t -> head_of_kind_value_non_null -> simple Generic_proof.t
      option **)

  let meet_block_field_simple_value min_name_mode field_kind field_index tenv =
    function
    | Variant (_, _, _, blocks, _, _) -> (
      match blocks with
      | Or_unknown.Known blocks0 -> (
        if row_like_for_blocks_is_bottom blocks0
        then Some Generic_proof.Invalid
        else
          match row_like_for_blocks_get_field blocks0 field_index with
          | Unknown -> Some Generic_proof.Unknown
          | Ok ty -> (
            if negb (kind_eqb (kind ty) field_kind)
            then Some Generic_proof.Invalid
            else
              match canonical_simple_of_alias tenv min_name_mode ty with
              | Some canonical -> (
                match canonical with
                | Some simple0 -> Some (Generic_proof.Proved simple0)
                | None -> Some Generic_proof.Unknown)
              | None -> None)
          | Bottom -> Some Generic_proof.Invalid)
      | Or_unknown.Unknown -> Some Generic_proof.Unknown)
    | Mutable_block _ -> Some Generic_proof.Unknown
    | _ -> Some Generic_proof.Invalid

  (** val meet_block_field_simple : Typing_env.t -> Name_mode.t -> flambda_kind
      -> flambda_type -> nat -> simple Meet_shortcut.t option **)

  let meet_block_field_simple tenv min_name_mode field_kind t0 field_index =
    gen_value_to_meet
      (meet_block_field_simple_value min_name_mode field_kind field_index)
      tenv t0

  (** val single_closures_entry_of_singleton : Alloc_mode.t -> bool ->
      function_slot -> closures_entry -> (((function_slot * Alloc_mode.t) *
      closures_entry) * function_type) Generic_proof.t **)

  let single_closures_entry_of_singleton alloc_mode exact slot entry =
    match closures_entry_find_function_type entry exact slot with
    | Unknown -> Generic_proof.Unknown
    | Ok function_type0 ->
      Generic_proof.Proved (((slot, alloc_mode), entry), function_type0)
    | Bottom -> Generic_proof.Invalid

  (** val prove_single_closures_entry_generic_value : Typing_env.t ->
      head_of_kind_value_non_null -> (((function_slot * Alloc_mode.t) *
      closures_entry) * function_type) Generic_proof.t option **)

  let prove_single_closures_entry_generic_value _ = function
    | Closures (by_function_slot, alloc_mode) -> (
      match row_like_for_closures_get_single_tag by_function_slot with
      | Some single -> (
        match single with
        | No_singleton -> Some Generic_proof.Unknown
        | Exact_closure (slot, entry) ->
          Some (single_closures_entry_of_singleton alloc_mode true slot entry)
        | Incomplete_closure (slot, entry) ->
          Some (single_closures_entry_of_singleton alloc_mode false slot entry))
      | None -> None)
    | _ -> Some Generic_proof.Invalid

  (** val prove_single_closures_entry : Typing_env.t -> flambda_type ->
      (((function_slot * Alloc_mode.t) * closures_entry) * function_type)
      Proof_of_property.t option **)

  let prove_single_closures_entry tenv t0 =
    gen_value_to_proof prove_single_closures_entry_generic_value tenv t0

  (** val meet_project_function_slot_simple_value : Name_mode.t -> function_slot
      -> Typing_env.t -> head_of_kind_value_non_null -> simple Generic_proof.t
      option **)

  let meet_project_function_slot_simple_value min_name_mode slot tenv = function
    | Closures (by_function_slot, _) -> (
      match row_like_for_closures_get_closure by_function_slot slot with
      | Some closure -> (
        match closure with
        | Or_unknown.Known ty -> (
          match canonical_simple_of_alias tenv min_name_mode ty with
          | Some canonical -> (
            match canonical with
            | Some simple0 -> Some (Generic_proof.Proved simple0)
            | None -> Some Generic_proof.Unknown)
          | None -> None)
        | Or_unknown.Unknown -> Some Generic_proof.Unknown)
      | None -> None)
    | _ -> Some Generic_proof.Invalid

  (** val meet_project_function_slot_simple : Typing_env.t -> Name_mode.t ->
      flambda_type -> function_slot -> simple Meet_shortcut.t option **)

  let meet_project_function_slot_simple tenv min_name_mode t0 slot =
    gen_value_to_meet
      (meet_project_function_slot_simple_value min_name_mode slot)
      tenv t0

  (** val meet_project_value_slot_simple_value : Name_mode.t -> value_slot ->
      flambda_kind -> Typing_env.t -> head_of_kind_value_non_null -> simple
      Generic_proof.t option **)

  let meet_project_value_slot_simple_value min_name_mode slot value_slot_kind
      tenv = function
    | Closures (by_function_slot, _) -> (
      match row_like_for_closures_get_env_var by_function_slot slot with
      | Some env_var -> (
        match env_var with
        | Or_unknown.Known ty -> (
          if negb (kind_eqb (kind ty) value_slot_kind)
          then Some Generic_proof.Invalid
          else
            match canonical_simple_of_alias tenv min_name_mode ty with
            | Some canonical -> (
              match canonical with
              | Some simple0 -> Some (Generic_proof.Proved simple0)
              | None -> Some Generic_proof.Unknown)
            | None -> None)
        | Or_unknown.Unknown -> Some Generic_proof.Unknown)
      | None -> None)
    | _ -> Some Generic_proof.Invalid

  (** val meet_project_value_slot_simple : Typing_env.t -> Name_mode.t ->
      flambda_type -> value_slot -> flambda_kind -> simple Meet_shortcut.t
      option **)

  let meet_project_value_slot_simple tenv min_name_mode t0 slot value_slot_kind
      =
    gen_value_to_meet
      (meet_project_value_slot_simple_value min_name_mode slot value_slot_kind)
      tenv t0

  (** val incompatible_naked_numbers : Typing_env.t -> flambda_type ->
      flambda_type -> bool option **)

  let incompatible_naked_numbers tenv t1 t2 =
    match expand_head tenv t1 with
    | Some expanded1 -> (
      match expand_head tenv t2 with
      | Some expanded2 -> (
        match expanded1 with
        | Oub_naked_number (k1, head) -> (
          match head with
          | Ok s1 -> (
            match expanded2 with
            | Oub_naked_number (k2, head0) -> (
              match head0 with
              | Ok s2 ->
                Some
                  (naked_number_kind_eqb k1 k2
                  && Keyed.is_empty (Keyed.inter Z.eqb s1 s2))
              | _ -> Some false)
            | _ -> Some false)
          | _ -> Some false)
        | _ -> Some false)
      | None -> None)
    | None -> None

  (** val physical_equality_of_immediates : Typing_env.t -> flambda_type ->
      flambda_type -> bool Generic_proof.t option **)

  let physical_equality_of_immediates tenv imms1 imms2 =
    match prove_naked_immediates_generic tenv imms1 with
    | Some proof1 -> (
      match prove_naked_immediates_generic tenv imms2 with
      | Some proof2 -> (
        match proof1 with
        | Generic_proof.Proved imms3 -> (
          match proof2 with
          | Generic_proof.Proved imms4 -> (
            if Keyed.is_empty (Keyed.inter Z.eqb imms3 imms4)
            then Some (Generic_proof.Proved false)
            else
              match Keyed.get_singleton Z.eqb imms3 with
              | Some imm1 -> (
                match Keyed.get_singleton Z.eqb imms4 with
                | Some imm2 ->
                  if Z.eqb imm1 imm2
                  then Some (Generic_proof.Proved true)
                  else None
                | None -> Some Generic_proof.Unknown)
              | None -> Some Generic_proof.Unknown)
          | Generic_proof.Unknown -> Some Generic_proof.Unknown
          | Generic_proof.Invalid -> Some (Generic_proof.Proved false))
        | Generic_proof.Unknown -> (
          match proof2 with
          | Generic_proof.Invalid -> Some (Generic_proof.Proved false)
          | _ -> Some Generic_proof.Unknown)
        | Generic_proof.Invalid -> (
          match proof2 with
          | Generic_proof.Invalid -> Some Generic_proof.Invalid
          | _ -> Some (Generic_proof.Proved false)))
      | None -> None)
    | None -> None

  (** val physical_equality_of_blocks : row_like_for_blocks ->
      row_like_for_blocks -> bool Generic_proof.t **)

  let physical_equality_of_blocks blocks1 blocks2 =
    let is_bottom1 = row_like_for_blocks_is_bottom blocks1 in
    let is_bottom2 = row_like_for_blocks_is_bottom blocks2 in
    if is_bottom1 && is_bottom2
    then Generic_proof.Invalid
    else if is_bottom1 || is_bottom2
    then Generic_proof.Proved false
    else
      match row_like_for_blocks_get_singleton blocks1 with
      | Some p -> (
        let p0, _ = p in
        let p1, _ = p0 in
        let p2, size1 = p1 in
        let tag1, shape1 = p2 in
        match row_like_for_blocks_get_singleton blocks2 with
        | Some p3 ->
          let p4, _ = p3 in
          let p5, _ = p4 in
          let p6, size2 = p5 in
          let tag2, shape2 = p6 in
          if
            (Z.eqb tag1 tag2 && Nat.eqb size1 size2)
            && block_shape_eqb shape1 shape2
          then Generic_proof.Unknown
          else Generic_proof.Proved false
        | None -> Generic_proof.Unknown)
      | None -> Generic_proof.Unknown

  (** val no_immediate_and_no_block : flambda_type Or_unknown.t ->
      row_like_for_blocks Or_unknown.t -> bool **)

  let no_immediate_and_no_block immediates blocks =
    match immediates with
    | Or_unknown.Known imms -> (
      match blocks with
      | Or_unknown.Known blocks0 ->
        is_obviously_bottom imms && row_like_for_blocks_is_bottom blocks0
      | Or_unknown.Unknown -> false)
    | Or_unknown.Unknown -> false

  (** val physical_equality_of_parts : bool Generic_proof.t -> bool
      Generic_proof.t -> bool Proof_of_property.t **)

  let physical_equality_of_parts immediates_equality blocks_equality =
    match immediates_equality with
    | Generic_proof.Proved b -> (
      if b
      then
        match blocks_equality with
        | Generic_proof.Invalid -> Proof_of_property.Proved b
        | _ -> Proof_of_property.Unknown
      else
        match blocks_equality with
        | Generic_proof.Proved a ->
          if a
          then Proof_of_property.Unknown
          else Proof_of_property.Proved false
        | Generic_proof.Unknown -> Proof_of_property.Unknown
        | Generic_proof.Invalid -> Proof_of_property.Proved b)
    | Generic_proof.Unknown -> Proof_of_property.Unknown
    | Generic_proof.Invalid -> (
      match blocks_equality with
      | Generic_proof.Proved b -> Proof_of_property.Proved b
      | _ -> Proof_of_property.Unknown)

  (** val physical_equality_of_variants : Typing_env.t -> flambda_type
      Or_unknown.t -> flambda_type Or_unknown.t -> row_like_for_blocks
      Or_unknown.t -> row_like_for_blocks Or_unknown.t -> bool
      Proof_of_property.t option **)

  let physical_equality_of_variants tenv immediates1 immediates2 blocks1 blocks2
      =
    if no_immediate_and_no_block immediates1 blocks2
    then Some (Proof_of_property.Proved false)
    else if no_immediate_and_no_block immediates2 blocks1
    then Some (Proof_of_property.Proved false)
    else
      match immediates1 with
      | Or_unknown.Known imms1 -> (
        match immediates2 with
        | Or_unknown.Known imms2 -> (
          match blocks1 with
          | Or_unknown.Known blocks3 -> (
            match blocks2 with
            | Or_unknown.Known blocks4 -> (
              match physical_equality_of_immediates tenv imms1 imms2 with
              | Some immediates_equality ->
                let blocks_equality =
                  physical_equality_of_blocks blocks3 blocks4
                in
                Some
                  (physical_equality_of_parts immediates_equality
                     blocks_equality)
              | None -> None)
            | Or_unknown.Unknown -> Some Proof_of_property.Unknown)
          | Or_unknown.Unknown -> Some Proof_of_property.Unknown)
        | Or_unknown.Unknown -> Some Proof_of_property.Unknown)
      | Or_unknown.Unknown -> Some Proof_of_property.Unknown

  (** val physical_equality_of_heads : Typing_env.t ->
      head_of_kind_value_non_null -> head_of_kind_value_non_null -> bool
      Proof_of_property.t option **)

  let physical_equality_of_heads tenv head1 head2 =
    match head1 with
    | Variant (_, immediates1, _, blocks, _, _) -> (
      match head2 with
      | Variant (_, immediates2, _, blocks2, _, _) ->
        physical_equality_of_variants tenv immediates1 immediates2 blocks
          blocks2
      | Mutable_block _ -> (
        match blocks with
        | Or_unknown.Known blocks0 ->
          if row_like_for_blocks_is_bottom blocks0
          then Some (Proof_of_property.Proved false)
          else Some Proof_of_property.Unknown
        | Or_unknown.Unknown -> Some Proof_of_property.Unknown)
      | _ -> Some (Proof_of_property.Proved false))
    | Mutable_block _ -> (
      match head2 with
      | Variant (_, _, _, blocks, _, _) -> (
        match blocks with
        | Or_unknown.Known blocks0 ->
          if row_like_for_blocks_is_bottom blocks0
          then Some (Proof_of_property.Proved false)
          else Some Proof_of_property.Unknown
        | Or_unknown.Unknown -> Some Proof_of_property.Unknown)
      | Mutable_block _ -> Some Proof_of_property.Unknown
      | _ -> Some (Proof_of_property.Proved false))
    | Boxed_number (k1, contents1, _) -> (
      match head2 with
      | Boxed_number (k2, contents2, _) ->
        if boxable_number_eqb k1 k2
        then
          match incompatible_naked_numbers tenv contents1 contents2 with
          | Some incompatible ->
            if incompatible
            then Some (Proof_of_property.Proved false)
            else Some Proof_of_property.Unknown
          | None -> None
        else Some (Proof_of_property.Proved false)
      | _ -> Some (Proof_of_property.Proved false))
    | Closures (_, _) -> (
      match head2 with
      | Closures (_, _) -> Some Proof_of_property.Unknown
      | _ -> Some (Proof_of_property.Proved false))
    | String strs1 -> (
      match head2 with
      | String strs2 ->
        if Keyed.is_empty (Keyed.inter (lists_eqb Z.eqb) strs1 strs2)
        then Some (Proof_of_property.Proved false)
        else Some Proof_of_property.Unknown
      | _ -> Some (Proof_of_property.Proved false))

  (** val physical_equality_check_heads : Typing_env.t -> flambda_type ->
      flambda_type -> bool Proof_of_property.t option **)

  let physical_equality_check_heads tenv t1 t2 =
    match expand_head tenv t1 with
    | Some expanded1 -> (
      match expand_head tenv t2 with
      | Some expanded2 -> (
        match expanded1 with
        | Oub_value head -> (
          match head with
          | Ok a -> (
            let (Head_of_kind_value (non_null1, is_null1)) = a in
            match expanded2 with
            | Oub_value head0 -> (
              match head0 with
              | Ok a0 -> (
                let (Head_of_kind_value (non_null2, is_null2)) = a0 in
                match is_null1 with
                | Not_null -> (
                  match is_null2 with
                  | Not_null -> (
                    match non_null1 with
                    | Ok head1 -> (
                      match non_null2 with
                      | Ok head2 -> physical_equality_of_heads tenv head1 head2
                      | _ -> Some Proof_of_property.Unknown)
                    | _ -> Some Proof_of_property.Unknown)
                  | Maybe_null _ -> Some Proof_of_property.Unknown)
                | Maybe_null _ -> (
                  match is_null2 with
                  | Not_null -> Some Proof_of_property.Unknown
                  | Maybe_null _ -> (
                    match non_null1 with
                    | Bottom -> (
                      match non_null2 with
                      | Bottom -> Some (Proof_of_property.Proved true)
                      | _ -> Some Proof_of_property.Unknown)
                    | _ -> Some Proof_of_property.Unknown)))
              | _ -> Some Proof_of_property.Unknown)
            | _ -> Some (wrong_kind Proof_of_property.Unknown))
          | _ -> (
            match expanded2 with
            | Oub_value _ -> Some Proof_of_property.Unknown
            | _ -> Some (wrong_kind Proof_of_property.Unknown)))
        | _ -> Some (wrong_kind Proof_of_property.Unknown))
      | None -> None)
    | None -> None

  (** val prove_physical_equality : Typing_env.t -> flambda_type -> flambda_type
      -> bool Proof_of_property.t option **)

  let prove_physical_equality tenv t1 t2 =
    match get_alias_opt t1 with
    | Some s1 -> (
      match get_alias_opt t2 with
      | Some s2 -> (
        match s1 with
        | Var var1 -> (
          match s2 with
          | Var var2 ->
            if Pos.eqb var1 var2
            then Some (Proof_of_property.Proved true)
            else physical_equality_check_heads tenv t1 t2
          | _ -> physical_equality_check_heads tenv t1 t2)
        | Symbol sym1 -> (
          match s2 with
          | Var _ -> physical_equality_check_heads tenv t1 t2
          | Symbol sym2 -> Some (Proof_of_property.Proved (Pos.eqb sym1 sym2))
          | Const _ -> Some (Proof_of_property.Proved false))
        | Const c1 -> (
          match s2 with
          | Var _ -> physical_equality_check_heads tenv t1 t2
          | Symbol _ -> Some (Proof_of_property.Proved false)
          | Const c2 -> Some (Proof_of_property.Proved (const_eqb c1 c2))))
      | None -> physical_equality_check_heads tenv t1 t2)
    | None -> physical_equality_check_heads tenv t1 t2
end
