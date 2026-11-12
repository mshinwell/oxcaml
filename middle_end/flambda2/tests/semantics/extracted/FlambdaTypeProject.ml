open BinNums
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open List

(** val traverse : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec traverse f = function
  | [] -> Some []
  | x :: l0 -> (
    match f x with
    | Some y -> (
      match traverse f l0 with Some l1 -> Some (y :: l1) | None -> None)
    | None -> None)

(** val project_relation : variable list -> (variable -> flambda_type option) ->
    variable option -> variable option option **)

let project_relation to_project expand relation =
  match relation with
  | Some var -> (
    if negb (among var to_project)
    then Some relation
    else
      match expand var with
      | Some ty ->
        Some
          (match get_alias_opt ty with
          | Some s -> ( match s with Var var' -> Some var' | _ -> None)
          | None -> None)
      | None -> None)
  | None -> Some None

(** val project_inverse_relation : variable list -> (variable -> flambda_type
    option) -> (Relation.t * name) -> (Relation.t * name) list option **)

let project_inverse_relation to_project expand pair =
  match snd pair with
  | Name_var var -> (
    if negb (among var to_project)
    then Some (pair :: [])
    else
      match expand var with
      | Some ty ->
        Some
          (match get_alias_opt ty with
          | Some s -> (
            match s with
            | Var var' -> (fst pair, Name_var var') :: []
            | Symbol symbol -> (fst pair, Name_symbol symbol) :: []
            | Const _ -> [])
          | None -> [])
      | None -> None)
  | Name_symbol _ -> Some (pair :: [])

(** val project_head_of_kind_naked_immediate : variable list -> (variable ->
    flambda_type option) -> head_of_kind_naked_immediate ->
    head_of_kind_naked_immediate option **)

let project_head_of_kind_naked_immediate to_project expand head =
  match
    traverse (project_inverse_relation to_project expand) head.inverse_relations
  with
  | Some relations ->
    Some
      { naked_immediates = head.naked_immediates;
        inverse_relations = concat relations
      }
  | None -> None

(** val project_descr : variable list -> (variable -> flambda_type option) ->
    ('a1 -> 'a1 option) -> (flambda_type -> 'a1 type_descr option) -> 'a1
    type_descr -> 'a1 type_descr option **)

let project_descr to_project expand project_head of_expanded ty =
  match ty with
  | Ok a -> (
    match a with
    | No_alias head -> (
      match project_head head with
      | Some head0 -> Some (Ok (No_alias head0))
      | None -> None)
    | Equals s -> (
      match s with
      | Var var ->
        if among var to_project
        then
          match expand var with
          | Some expanded -> of_expanded expanded
          | None -> None
        else Some ty
      | _ -> Some ty))
  | _ -> Some ty

(** val value_of_expanded : flambda_type -> head_of_kind_value type_descr option
    **)

let value_of_expanded = function Type_value ty0 -> Some ty0 | _ -> None

(** val naked_immediate_of_expanded : flambda_type ->
    head_of_kind_naked_immediate type_descr option **)

let naked_immediate_of_expanded = function
  | Type_naked_immediate ty0 -> Some ty0
  | _ -> None

(** val naked_number_of_expanded : naked_number_kind -> flambda_type -> coq_Z
    list type_descr option **)

let naked_number_of_expanded k = function
  | Type_naked_number (k', ty0) ->
    if kind_eqb (Naked_number k) (Naked_number k') then Some ty0 else None
  | _ -> None

(** val rec_info_of_expanded : flambda_type -> unit type_descr option **)

let rec_info_of_expanded = function Type_rec_info ty0 -> Some ty0 | _ -> None

(** val region_of_expanded : flambda_type -> unit type_descr option **)

let region_of_expanded = function Type_region ty0 -> Some ty0 | _ -> None

(** val project_block_case : (flambda_type -> flambda_type option) ->
    (env_extension -> env_extension option) -> row_like_block_case ->
    row_like_block_case option **)

let project_block_case project_variables_out0 project_env_extension case =
  match project_env_extension case.case_env_extension with
  | Some env_extension0 -> (
    match traverse project_variables_out0 case.case_maps_to with
    | Some maps_to ->
      Some
        { case_maps_to = maps_to;
          case_index = case.case_index;
          case_env_extension = env_extension0
        }
    | None -> None)
  | None -> None

(** val project_variables_out : variable list -> (variable -> flambda_type
    option) -> flambda_type -> flambda_type option **)

let project_variables_out to_project expand =
  let rec project_variables_out0 = function
    | Type_value ty -> (
      match
        project_descr to_project expand project_head_of_kind_value
          value_of_expanded ty
      with
      | Some ty0 -> Some (Type_value ty0)
      | None -> None)
    | Type_naked_immediate ty -> (
      match
        project_descr to_project expand
          (project_head_of_kind_naked_immediate to_project expand)
          naked_immediate_of_expanded ty
      with
      | Some ty0 -> Some (Type_naked_immediate ty0)
      | None -> None)
    | Type_naked_number (k, ty) -> (
      match
        project_descr to_project expand
          (fun head -> Some head)
          (naked_number_of_expanded k)
          ty
      with
      | Some ty0 -> Some (Type_naked_number (k, ty0))
      | None -> None)
    | Type_rec_info ty -> (
      match
        project_descr to_project expand
          (fun head -> Some head)
          rec_info_of_expanded ty
      with
      | Some ty0 -> Some (Type_rec_info ty0)
      | None -> None)
    | Type_region ty -> (
      match
        project_descr to_project expand
          (fun head -> Some head)
          region_of_expanded ty
      with
      | Some ty0 -> Some (Type_region ty0)
      | None -> None)
  and project_head_of_kind_value = function
    | Head_of_kind_value (non_null, is_null) -> (
      match is_null with
      | Not_null -> (
        let is_null0 = Not_null in
        match non_null with
        | Unknown ->
          let non_null0 = Unknown in
          Some (Head_of_kind_value (non_null0, is_null0))
        | Ok non_null_head -> (
          match project_head_of_kind_value_non_null non_null_head with
          | Some non_null_head0 ->
            let non_null0 = Ok non_null_head0 in
            Some (Head_of_kind_value (non_null0, is_null0))
          | None -> None)
        | Bottom ->
          let non_null0 = Bottom in
          Some (Head_of_kind_value (non_null0, is_null0)))
      | Maybe_null is_null_var -> (
        match project_relation to_project expand is_null_var with
        | Some is_null_var0 -> (
          let is_null0 = Maybe_null is_null_var0 in
          match non_null with
          | Unknown ->
            let non_null0 = Unknown in
            Some (Head_of_kind_value (non_null0, is_null0))
          | Ok non_null_head -> (
            match project_head_of_kind_value_non_null non_null_head with
            | Some non_null_head0 ->
              let non_null0 = Ok non_null_head0 in
              Some (Head_of_kind_value (non_null0, is_null0))
            | None -> None)
          | Bottom ->
            let non_null0 = Bottom in
            Some (Head_of_kind_value (non_null0, is_null0)))
        | None -> None))
  and project_head_of_kind_value_non_null head =
    match head with
    | Variant (is_int, immediates, get_tag, blocks, extensions, is_unique) -> (
      match project_relation to_project expand is_int with
      | Some is_int0 -> (
        match project_relation to_project expand get_tag with
        | Some get_tag0 -> (
          match immediates with
          | Or_unknown.Known immediates0 -> (
            match project_variables_out0 immediates0 with
            | Some immediates1 -> (
              let immediates2 = Or_unknown.Known immediates1 in
              match blocks with
              | Or_unknown.Known blocks0 -> (
                match project_row_like_for_blocks blocks0 with
                | Some blocks1 -> (
                  let blocks2 = Or_unknown.Known blocks1 in
                  match extensions with
                  | No_extensions ->
                    let extensions0 = No_extensions in
                    Some
                      (Variant
                         ( is_int0,
                           immediates2,
                           get_tag0,
                           blocks2,
                           extensions0,
                           is_unique ))
                  | Ext (when_immediate, when_block) -> (
                    match project_env_extension when_immediate with
                    | Some when_immediate0 -> (
                      match project_env_extension when_block with
                      | Some when_block0 ->
                        let extensions0 = Ext (when_immediate0, when_block0) in
                        Some
                          (Variant
                             ( is_int0,
                               immediates2,
                               get_tag0,
                               blocks2,
                               extensions0,
                               is_unique ))
                      | None -> None)
                    | None -> None))
                | None -> None)
              | Or_unknown.Unknown -> (
                let blocks0 = Or_unknown.Unknown in
                match extensions with
                | No_extensions ->
                  let extensions0 = No_extensions in
                  Some
                    (Variant
                       ( is_int0,
                         immediates2,
                         get_tag0,
                         blocks0,
                         extensions0,
                         is_unique ))
                | Ext (when_immediate, when_block) -> (
                  match project_env_extension when_immediate with
                  | Some when_immediate0 -> (
                    match project_env_extension when_block with
                    | Some when_block0 ->
                      let extensions0 = Ext (when_immediate0, when_block0) in
                      Some
                        (Variant
                           ( is_int0,
                             immediates2,
                             get_tag0,
                             blocks0,
                             extensions0,
                             is_unique ))
                    | None -> None)
                  | None -> None)))
            | None -> None)
          | Or_unknown.Unknown -> (
            let immediates0 = Or_unknown.Unknown in
            match blocks with
            | Or_unknown.Known blocks0 -> (
              match project_row_like_for_blocks blocks0 with
              | Some blocks1 -> (
                let blocks2 = Or_unknown.Known blocks1 in
                match extensions with
                | No_extensions ->
                  let extensions0 = No_extensions in
                  Some
                    (Variant
                       ( is_int0,
                         immediates0,
                         get_tag0,
                         blocks2,
                         extensions0,
                         is_unique ))
                | Ext (when_immediate, when_block) -> (
                  match project_env_extension when_immediate with
                  | Some when_immediate0 -> (
                    match project_env_extension when_block with
                    | Some when_block0 ->
                      let extensions0 = Ext (when_immediate0, when_block0) in
                      Some
                        (Variant
                           ( is_int0,
                             immediates0,
                             get_tag0,
                             blocks2,
                             extensions0,
                             is_unique ))
                    | None -> None)
                  | None -> None))
              | None -> None)
            | Or_unknown.Unknown -> (
              let blocks0 = Or_unknown.Unknown in
              match extensions with
              | No_extensions ->
                let extensions0 = No_extensions in
                Some
                  (Variant
                     ( is_int0,
                       immediates0,
                       get_tag0,
                       blocks0,
                       extensions0,
                       is_unique ))
              | Ext (when_immediate, when_block) -> (
                match project_env_extension when_immediate with
                | Some when_immediate0 -> (
                  match project_env_extension when_block with
                  | Some when_block0 ->
                    let extensions0 = Ext (when_immediate0, when_block0) in
                    Some
                      (Variant
                         ( is_int0,
                           immediates0,
                           get_tag0,
                           blocks0,
                           extensions0,
                           is_unique ))
                  | None -> None)
                | None -> None))))
        | None -> None)
      | None -> None)
    | Boxed_number (k, contents, alloc_mode) -> (
      match project_variables_out0 contents with
      | Some contents0 -> Some (Boxed_number (k, contents0, alloc_mode))
      | None -> None)
    | Closures (by_function_slot, alloc_mode) -> (
      match project_row_like_for_closures by_function_slot with
      | Some by_function_slot0 ->
        Some (Closures (by_function_slot0, alloc_mode))
      | None -> None)
    | _ -> Some head
  and project_row_like_for_blocks = function
    | Row_like_for_blocks (known_tags, other_tags, alloc_mode) -> (
      match
        traverse
          (fun binding ->
            match snd binding with
            | Or_unknown.Known case -> (
              match
                project_block_case project_variables_out0 project_env_extension
                  case
              with
              | Some case0 -> Some (fst binding, Or_unknown.Known case0)
              | None -> None)
            | Or_unknown.Unknown -> Some (fst binding, Or_unknown.Unknown))
          known_tags
      with
      | Some known_tags0 -> (
        match other_tags with
        | Or_bottom.Ok case -> (
          match
            project_block_case project_variables_out0 project_env_extension case
          with
          | Some case0 ->
            let other_tags0 = Or_bottom.Ok case0 in
            Some (Row_like_for_blocks (known_tags0, other_tags0, alloc_mode))
          | None -> None)
        | Or_bottom.Bottom ->
          let other_tags0 = Or_bottom.Bottom in
          Some (Row_like_for_blocks (known_tags0, other_tags0, alloc_mode)))
      | None -> None)
  and project_row_like_for_closures = function
    | Row_like_for_closures known_closures -> (
      match
        traverse
          (fun binding ->
            match project_env_extension (snd binding).case_env_extension with
            | Some env_extension0 -> (
              match project_closures_entry (snd binding).case_maps_to with
              | Some maps_to ->
                Some
                  ( fst binding,
                    { case_maps_to = maps_to;
                      case_index = (snd binding).case_index;
                      case_env_extension = env_extension0
                    } )
              | None -> None)
            | None -> None)
          known_closures
      with
      | Some known_closures0 -> Some (Row_like_for_closures known_closures0)
      | None -> None)
  and project_closures_entry = function
    | Closures_entry (function_types, closure_types, value_slot_types) -> (
      match
        traverse
          (fun binding ->
            match project_variables_out0 (snd binding) with
            | Some ty -> Some (fst binding, ty)
            | None -> None)
          closure_types
      with
      | Some closure_types0 -> (
        match
          traverse
            (fun binding ->
              match project_variables_out0 (snd binding) with
              | Some ty -> Some (fst binding, ty)
              | None -> None)
            value_slot_types
        with
        | Some value_slot_types0 ->
          Some
            (Closures_entry (function_types, closure_types0, value_slot_types0))
        | None -> None)
      | None -> None)
  and project_env_extension = function
    | Env_extension equations -> (
      match
        traverse
          (fun binding ->
            let keep_equation =
              match project_variables_out0 (snd binding) with
              | Some ty -> Some ((fst binding, ty) :: [])
              | None -> None
            in
            match fst binding with
            | Name_var var ->
              if among var to_project then Some [] else keep_equation
            | Name_symbol _ -> keep_equation)
          equations
      with
      | Some equations0 -> Some (Env_extension (concat equations0))
      | None -> None)
  in
  project_variables_out0
