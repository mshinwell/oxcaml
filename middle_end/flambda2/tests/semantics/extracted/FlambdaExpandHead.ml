open BinNums
open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv

module Expanded_type = struct
  type head =
    | Head_value of head_of_kind_value
    | Head_naked_immediate of head_of_kind_naked_immediate
    | Head_naked_number of naked_number_kind * coq_Z list
    | Head_rec_info of unit
    | Head_region of unit

  (** val head_rect : (head_of_kind_value -> 'a1) ->
      (head_of_kind_naked_immediate -> 'a1) -> (naked_number_kind -> coq_Z list
      -> 'a1) -> (unit -> 'a1) -> (unit -> 'a1) -> head -> 'a1 **)

  let head_rect head_value head_naked_immediate head_naked_number head_rec_info
      head_region = function
    | Head_value head0 -> head_value head0
    | Head_naked_immediate head0 -> head_naked_immediate head0
    | Head_naked_number (k, head0) -> head_naked_number k head0
    | Head_rec_info head0 -> head_rec_info head0
    | Head_region head0 -> head_region head0

  (** val head_rec : (head_of_kind_value -> 'a1) ->
      (head_of_kind_naked_immediate -> 'a1) -> (naked_number_kind -> coq_Z list
      -> 'a1) -> (unit -> 'a1) -> (unit -> 'a1) -> head -> 'a1 **)

  let head_rec head_value head_naked_immediate head_naked_number head_rec_info
      head_region = function
    | Head_value head0 -> head_value head0
    | Head_naked_immediate head0 -> head_naked_immediate head0
    | Head_naked_number (k, head0) -> head_naked_number k head0
    | Head_rec_info head0 -> head_rec_info head0
    | Head_region head0 -> head_region head0

  type t =
    { kind : flambda_kind;
      descr : head or_unknown_or_bottom
    }

  (** val kind : t -> flambda_kind **)

  let kind t0 = t0.kind

  (** val descr : t -> head or_unknown_or_bottom **)

  let descr t0 = t0.descr

  (** val create_bottom : flambda_kind -> t **)

  let create_bottom kind0 = { kind = kind0; descr = Bottom }

  (** val create_unknown : flambda_kind -> t **)

  let create_unknown kind0 = { kind = kind0; descr = Unknown }

  (** val create_value : head_of_kind_value -> t **)

  let create_value head0 = { kind = Value; descr = Ok (Head_value head0) }

  (** val create_naked_immediate : head_of_kind_naked_immediate -> t **)

  let create_naked_immediate head0 =
    { kind = Naked_number Kind_naked_immediate;
      descr = Ok (Head_naked_immediate head0)
    }

  (** val create_naked_number : naked_number_kind -> coq_Z list -> t **)

  let create_naked_number k head0 =
    { kind = Naked_number k; descr = Ok (Head_naked_number (k, head0)) }

  (** val create_rec_info : unit -> t **)

  let create_rec_info head0 =
    { kind = Rec_info; descr = Ok (Head_rec_info head0) }

  (** val create_region : unit -> t **)

  let create_region head0 = { kind = Region; descr = Ok (Head_region head0) }

  (** val create_const : const -> t **)

  let create_const = function
    | Naked_immediate i ->
      create_naked_immediate
        { naked_immediates = Or_unknown.Known (i :: []);
          inverse_relations = []
        }
    | Tagged_immediate i -> create_value (head_of_kind_value_tagged_immediate i)
    | Naked_float32 f -> create_naked_number Kind_naked_float32 (f :: [])
    | Naked_float f -> create_naked_number Kind_naked_float (f :: [])
    | Naked_int8 i -> create_naked_number Kind_naked_int8 (i :: [])
    | Naked_int16 i -> create_naked_number Kind_naked_int16 (i :: [])
    | Naked_int32 i -> create_naked_number Kind_naked_int32 (i :: [])
    | Naked_int64 i -> create_naked_number Kind_naked_int64 (i :: [])
    | Naked_nativeint i -> create_naked_number Kind_naked_nativeint (i :: [])
    | Naked_vec128 i -> create_naked_number Kind_naked_vec128 (i :: [])
    | Naked_vec256 i -> create_naked_number Kind_naked_vec256 (i :: [])
    | Naked_vec512 i -> create_naked_number Kind_naked_vec512 (i :: [])
    | Naked_mask i -> create_naked_number Kind_naked_mask (i :: [])
    | Null -> create_value head_of_kind_value_null
    | Poison kind0 -> create_unknown kind0

  (** val bottom_like : t -> t **)

  let bottom_like expanded = create_bottom expanded.kind

  (** val unknown_like : t -> t **)

  let unknown_like expanded = create_unknown expanded.kind

  (** val is_bottom : t -> bool **)

  let is_bottom expanded =
    match expanded.descr with Bottom -> true | _ -> false

  (** val is_unknown : t -> bool **)

  let is_unknown expanded =
    match expanded.descr with Unknown -> true | _ -> false

  (** val to_type : t -> flambda_type **)

  let to_type expanded =
    match expanded.descr with
    | Unknown -> unknown expanded.kind
    | Ok a -> (
      match a with
      | Head_value head0 -> Type_value (Ok (No_alias head0))
      | Head_naked_immediate head0 -> Type_naked_immediate (Ok (No_alias head0))
      | Head_naked_number (k, head0) ->
        Type_naked_number (k, Ok (No_alias head0))
      | Head_rec_info head0 -> Type_rec_info (Ok (No_alias head0))
      | Head_region head0 -> Type_region (Ok (No_alias head0)))
    | Bottom -> bottom expanded.kind

  (** val of_non_alias_type : flambda_type -> t option **)

  let of_non_alias_type ty =
    let of_descr =
     fun k make ty0 ->
      match ty0 with
      | Unknown -> Some (create_unknown k)
      | Ok a -> (
        match a with
        | No_alias head0 -> Some { kind = k; descr = Ok (make head0) }
        | Equals _ -> None)
      | Bottom -> Some (create_bottom k)
    in
    match ty with
    | Type_value ty0 -> of_descr Value (fun x -> Head_value x) ty0
    | Type_naked_immediate ty0 ->
      of_descr (Naked_number Kind_naked_immediate)
        (fun x -> Head_naked_immediate x)
        ty0
    | Type_naked_number (k, ty0) ->
      of_descr (Naked_number k) (fun x -> Head_naked_number (k, x)) ty0
    | Type_rec_info ty0 -> of_descr Rec_info (fun x -> Head_rec_info x) ty0
    | Type_region ty0 -> of_descr Region (fun x -> Head_region x) ty0
end

(** val expand_head_of_alias_type : Typing_env.t -> flambda_kind -> simple ->
    Expanded_type.t option **)

let expand_head_of_alias_type tenv kind0 known_canonical_simple_at_in_types_mode
    =
  let of_name =
   fun name ->
    match Typing_env.find tenv name (Some kind0) with
    | Some ty -> Expanded_type.of_non_alias_type ty
    | None -> None
  in
  match known_canonical_simple_at_in_types_mode with
  | Var x -> of_name (Name_var x)
  | Symbol s -> of_name (Name_symbol s)
  | Const const0 -> Some (Expanded_type.create_const const0)

(** val expand_head0 : Typing_env.t -> flambda_type -> simple option ->
    Expanded_type.t option **)

let expand_head0 tenv ty known_canonical_simple_at_in_types_mode =
  match get_alias_opt ty with
  | Some _ -> (
    match known_canonical_simple_at_in_types_mode with
    | Some simple0 -> expand_head_of_alias_type tenv (kind ty) simple0
    | None -> Expanded_type.of_non_alias_type (unknown (kind ty)))
  | None -> Expanded_type.of_non_alias_type ty

(** val expand_head : Typing_env.t -> flambda_type -> Expanded_type.t option **)

let expand_head tenv ty =
  match get_alias_opt ty with
  | Some simple0 -> (
    let kind0 = kind ty in
    match
      Typing_env.get_canonical_simple_exn tenv (Some Name_mode.in_types) None
        simple0
    with
    | Some canonical -> (
      match canonical with
      | Some simple1 -> expand_head_of_alias_type tenv kind0 simple1
      | None -> Expanded_type.of_non_alias_type (unknown kind0))
    | None -> None)
  | None -> Expanded_type.of_non_alias_type ty
