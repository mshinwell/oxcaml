open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaExpandHead
open FlambdaJoinEnv
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypeMeaningBoolSpec
open FlambdaTypingEnv
open List
open ListDef
open PeanoNat
module Expanded_type = Expanded_type

(** val known_function_types : (Index.t * function_type Or_unknown.t) list ->
    function_type list option **)

let rec known_function_types = function
  | [] -> Some []
  | p :: func_types0 -> (
    let _, t0 = p in
    match t0 with
    | Or_unknown.Known func_type -> (
      match known_function_types func_types0 with
      | Some known -> Some (func_type :: known)
      | None -> None)
    | Or_unknown.Unknown -> None)

(** val n_way_join_function_type : (Index.t * function_type Or_unknown.t) list
    -> function_type Or_unknown.t **)

let n_way_join_function_type func_types =
  match known_function_types func_types with
  | Some l -> (
    match l with
    | [] -> Or_unknown.Unknown
    | func_type :: func_types0 ->
      if
        forallb
          (fun func_type' ->
            Pos.eqb func_type.function_type_code_id
              func_type'.function_type_code_id)
          func_types0
      then Or_unknown.Known func_type
      else Or_unknown.Unknown)
  | None -> Or_unknown.Unknown

(** val gather_function_types : (Index.t * function_type Or_unknown.t
    finite_map) list -> (Index.t * function_type Or_unknown.t) list finite_map **)

let gather_function_types = function
  | [] -> []
  | p :: entries0 ->
    let id1, function_types1 = p in
    fold_left
      (fun function_types entry ->
        merge
          (fun vals_opt val2_opt ->
            match vals_opt with
            | Some vals -> (
              match val2_opt with
              | Some val2 -> Some ((fst entry, val2) :: vals)
              | None -> None)
            | None -> None)
          function_types (snd entry))
      entries0
      (map_values (fun func_type -> (id1, func_type) :: []) function_types1)

(** val n_way_join_function_types : (Index.t * function_type Or_unknown.t
    finite_map) list -> function_type Or_unknown.t finite_map **)

let n_way_join_function_types entries =
  map_values n_way_join_function_type (gather_function_types entries)

(** val or_unknown_map : ('a1 -> 'a2) -> 'a1 Or_unknown.t -> 'a2 Or_unknown.t **)

let or_unknown_map f = function
  | Or_unknown.Known a0 -> Or_unknown.Known (f a0)
  | Or_unknown.Unknown -> Or_unknown.Unknown

(** val join_alloc_mode : Alloc_mode.t -> Alloc_mode.t -> Alloc_mode.t **)

let join_alloc_mode alloc_mode1 alloc_mode2 =
  match alloc_mode1 with
  | Alloc_mode.Heap -> (
    match alloc_mode2 with
    | Alloc_mode.Heap -> Alloc_mode.Heap
    | _ -> Alloc_mode.Heap_or_local)
  | _ -> Alloc_mode.Heap_or_local

(** val numbers_union : coq_Z list -> coq_Z list -> coq_Z list **)

let numbers_union numbers numbers' = Keyed.dedup Z.eqb (app numbers numbers')

(** val untagged_const_bool : bool -> simple **)

let untagged_const_bool b =
  Const (Naked_immediate (if b then Zpos Coq_xH else Z0))

(** val untagged_const_int : coq_Z -> simple **)

let untagged_const_int i = Const (Naked_immediate i)

(** val row_like_for_blocks_all_tags : row_like_for_blocks -> coq_Z list
    Or_unknown.t **)

let row_like_for_blocks_all_tags = function
  | Row_like_for_blocks (known_tags, other_tags, _) -> (
    match other_tags with
    | Or_bottom.Ok _ -> Or_unknown.Unknown
    | Or_bottom.Bottom -> Or_unknown.Known (Keyed.domain Z.eqb known_tags))

(** val deduce_is_int : row_like_for_blocks Or_unknown.t -> flambda_type
    Or_unknown.t -> bool Or_unknown.t **)

let deduce_is_int blocks imms =
  let no_blocks =
    match blocks with
    | Or_unknown.Known blocks0 -> row_like_for_blocks_is_bottom blocks0
    | Or_unknown.Unknown -> false
  in
  let no_immediates =
    match imms with
    | Or_unknown.Known imms0 -> is_obviously_bottom imms0
    | Or_unknown.Unknown -> false
  in
  if no_blocks
  then Or_unknown.Known true
  else if no_immediates
  then Or_unknown.Known false
  else Or_unknown.Unknown

(** val deduce_is_int_simple : row_like_for_blocks Or_unknown.t -> flambda_type
    Or_unknown.t -> variable option -> simple option **)

let deduce_is_int_simple blocks imms is_int_var =
  match deduce_is_int blocks imms with
  | Or_unknown.Known is_int -> Some (untagged_const_bool is_int)
  | Or_unknown.Unknown -> (
    match is_int_var with Some var -> Some (Var var) | None -> None)

(** val deduce_get_tag : row_like_for_blocks Or_unknown.t -> coq_Z
    or_unknown_or_bottom **)

let deduce_get_tag = function
  | Or_unknown.Known blocks0 -> (
    match row_like_for_blocks_all_tags blocks0 with
    | Or_unknown.Known all_tags -> (
      if Keyed.is_empty all_tags
      then Bottom
      else
        match Keyed.get_singleton Z.eqb all_tags with
        | Some tag -> Ok tag
        | None -> Unknown)
    | Or_unknown.Unknown -> Unknown)
  | Or_unknown.Unknown -> Unknown

(** val deduce_get_tag_simple : row_like_for_blocks Or_unknown.t -> variable
    option -> simple or_unknown_or_bottom **)

let deduce_get_tag_simple blocks get_tag_var =
  match deduce_get_tag blocks with
  | Unknown -> (
    match get_tag_var with Some var -> Ok (Var var) | None -> Unknown)
  | Ok get_tag -> Ok (untagged_const_int get_tag)
  | Bottom -> Bottom

(** val known_contents : (Index.t * 'a1) list -> (Index.t * 'a1 Or_unknown.t)
    list -> (Index.t * 'a1) list option **)

let rec known_contents acc = function
  | [] -> Some acc
  | p :: or_unknowns0 -> (
    let id, t0 = p in
    match t0 with
    | Or_unknown.Known contents ->
      known_contents ((id, contents) :: acc) or_unknowns0
    | Or_unknown.Unknown -> None)

(** val is_null_simples : (Index.t * head_of_kind_value) list -> (Index.t *
    simple) list option **)

let rec is_null_simples = function
  | [] -> Some []
  | p :: heads0 -> (
    let id, h = p in
    let (Head_of_kind_value (_, is_null0)) = h in
    match is_null0 with
    | Not_null ->
      option_map
        (fun x -> (id, untagged_const_bool false) :: x)
        (is_null_simples heads0)
    | Maybe_null is_null1 -> (
      match is_null1 with
      | Some is_null2 ->
        option_map (fun x -> (id, Var is_null2) :: x) (is_null_simples heads0)
      | None -> None))

(** val strings_union : coq_Z list list -> coq_Z list list -> coq_Z list list **)

let strings_union strs strs' = Keyed.dedup (lists_eqb Z.eqb) (app strs strs')

(** val unknown_from_shape : block_shape -> nat -> flambda_type option **)

let unknown_from_shape shape index =
  option_map unknown (block_shape_element_kind shape index)

(** val env_extension_is_empty : env_extension -> bool **)

let env_extension_is_empty = function
  | Env_extension equations -> Keyed.is_empty equations

(** val closures_entry_function_types : closures_entry -> function_type
    Or_unknown.t finite_map **)

let closures_entry_function_types = function
  | Closures_entry (function_types, _, _) -> function_types

(** val closures_entry_closure_types : closures_entry -> flambda_type finite_map
    **)

let closures_entry_closure_types = function
  | Closures_entry (_, closure_types, _) -> closure_types

(** val closures_entry_value_slot_types : closures_entry -> flambda_type
    finite_map **)

let closures_entry_value_slot_types = function
  | Closures_entry (_, _, value_slot_types) -> value_slot_types

(** val row_like_known_tags : row_like_for_blocks -> (coq_Z, row_like_block_case
    Or_unknown.t) Keyed.finite_map **)

let row_like_known_tags = function
  | Row_like_for_blocks (known_tags, _, _) -> known_tags

(** val row_like_other_tags : row_like_for_blocks -> row_like_block_case
    Or_bottom.t **)

let row_like_other_tags = function
  | Row_like_for_blocks (_, other_tags, _) -> other_tags

(** val row_like_alloc_mode : row_like_for_blocks -> Alloc_mode.t **)

let row_like_alloc_mode = function
  | Row_like_for_blocks (_, _, alloc_mode) -> alloc_mode

(** val row_like_known_closures : row_like_for_closures ->
    row_like_closures_case finite_map **)

let row_like_known_closures = function
  | Row_like_for_closures known_closures -> known_closures

(** val gather_components : (Index.t * 'a1 finite_map) list -> (Index.t * 'a1)
    list finite_map **)

let gather_components = function
  | [] -> []
  | p :: indexed_products0 ->
    let id1, indexed_product1 = p in
    fold_left
      (fun components_by_index indexed_product2 ->
        merge
          (fun vals_opt val2_opt ->
            match vals_opt with
            | Some vals -> (
              match val2_opt with
              | Some val2 -> Some ((fst indexed_product2, val2) :: vals)
              | None -> None)
            | None -> None)
          components_by_index (snd indexed_product2))
      indexed_products0
      (map_values (fun val1 -> (id1, val1) :: []) indexed_product1)

(** val add_other : ('a2 -> 'a1) -> (Index.t * 'a1) list -> Index.t -> 'a2
    Or_bottom.t -> (Index.t * 'a1) list **)

let add_other of_other acc id = function
  | Or_bottom.Ok known -> (id, of_other known) :: acc
  | Or_bottom.Bottom -> acc

(** val gather_known : ('a1 -> 'a1 -> bool) -> ('a3 -> 'a2) -> (Index.t * (('a1,
    'a2) Keyed.finite_map * 'a3 Or_bottom.t)) list -> ('a1, (Index.t * 'a2)
    list) Keyed.finite_map **)

let gather_known eqb0 of_other = function
  | [] -> []
  | p :: maps0 ->
    let id1, p0 = p in
    let map1, other1 = p0 in
    fst
      (fold_left
         (fun acc input ->
           let id2 = fst input in
           let map2 = fst (snd input) in
           let other2 = snd (snd input) in
           ( Keyed.merge eqb0
               (fun vals_opt val2_opt ->
                 match vals_opt with
                 | Some vals -> (
                   match val2_opt with
                   | Some val2 -> Some ((id2, val2) :: vals)
                   | None -> Some (add_other of_other vals id2 other2))
                 | None -> (
                   match val2_opt with
                   | Some val2 -> Some ((id2, val2) :: snd acc)
                   | None -> None))
               (fst acc) map2,
             add_other of_other (snd acc) id2 other2 ))
         maps0
         ( Keyed.map_values (fun val1 -> (id1, val1) :: []) map1,
           add_other of_other [] id1 other1 ))

(** val all_known : (Index.t * 'a1 Or_unknown.t) list -> (Index.t * 'a1) list
    option **)

let rec all_known = function
  | [] -> Some []
  | p :: or_unknowns0 -> (
    let id, t0 = p in
    match t0 with
    | Or_unknown.Known a ->
      option_map (fun x -> (id, a) :: x) (all_known or_unknowns0)
    | Or_unknown.Unknown -> None)

(** val non_bottom : (Index.t * 'a1) list -> (Index.t * 'a1 Or_bottom.t) list ->
    (Index.t * 'a1) list **)

let rec non_bottom acc = function
  | [] -> acc
  | p :: or_bottoms0 -> (
    let id, t0 = p in
    match t0 with
    | Or_bottom.Ok a -> non_bottom ((id, a) :: acc) or_bottoms0
    | Or_bottom.Bottom -> non_bottom acc or_bottoms0)

(** val gather_extensions : (Index.t * env_extension) list -> (Index.t *
    env_extension) list -> (Index.t * variant_extensions) list -> ((Index.t *
    env_extension) list * (Index.t * env_extension) list) option **)

let rec gather_extensions when_immediates when_blocks = function
  | [] -> Some (when_immediates, when_blocks)
  | p :: extensions0 -> (
    let id, v = p in
    match v with
    | No_extensions -> None
    | Ext (when_immediate, when_block) ->
      gather_extensions
        ((id, when_immediate) :: when_immediates)
        ((id, when_block) :: when_blocks)
        extensions0)

(** val non_null_heads : (Index.t * head_of_kind_value_non_null) list ->
    (Index.t * head_of_kind_value) list -> (Index.t *
    head_of_kind_value_non_null) list option **)

let rec non_null_heads acc = function
  | [] -> Some acc
  | p :: heads0 -> (
    let id2, h = p in
    let (Head_of_kind_value (non_null, _)) = h in
    match non_null with
    | Unknown -> None
    | Ok head0 -> non_null_heads ((id2, head0) :: acc) heads0
    | Bottom -> non_null_heads acc heads0)

(** val gather_heads : (head_of_kind_value_non_null -> 'a1 option) -> (Index.t
    -> 'a1 -> 'a2 -> 'a2) -> (Index.t * head_of_kind_value_non_null) list -> 'a2
    -> 'a2 option **)

let rec gather_heads read combine other_heads init =
  match other_heads with
  | [] -> Some init
  | p :: other_heads0 -> (
    let other_id, other_head = p in
    match gather_heads read combine other_heads0 init with
    | Some acc -> (
      match read other_head with
      | Some a -> Some (combine other_id a acc)
      | None -> None)
    | None -> None)

type variant_parts =
  { parts_blocks : (Index.t * row_like_for_blocks Or_unknown.t) list;
    parts_immediates : (Index.t * flambda_type Or_unknown.t) list;
    parts_extensions : (Index.t * variant_extensions) list;
    parts_is_unique : bool;
    parts_is_int : (Index.t * simple) list option;
    parts_get_tag : (Index.t * simple) list option
  }

type variant_fields =
  { variant_is_int : variable option;
    variant_immediates : flambda_type Or_unknown.t;
    variant_get_tag : variable option;
    variant_blocks : row_like_for_blocks Or_unknown.t;
    variant_extensions_of : variant_extensions;
    variant_is_unique : bool
  }

(** val read_variant : head_of_kind_value_non_null -> variant_fields option **)

let read_variant = function
  | Variant (is_int, immediates, get_tag, blocks, extensions, is_unique) ->
    Some
      { variant_is_int = is_int;
        variant_immediates = immediates;
        variant_get_tag = get_tag;
        variant_blocks = blocks;
        variant_extensions_of = extensions;
        variant_is_unique = is_unique
      }
  | _ -> None

(** val first_variant_parts : Index.t -> variant_fields -> variant_parts **)

let first_variant_parts first_id first =
  { parts_blocks = (first_id, first.variant_blocks) :: [];
    parts_immediates = (first_id, first.variant_immediates) :: [];
    parts_extensions = (first_id, first.variant_extensions_of) :: [];
    parts_is_unique = first.variant_is_unique;
    parts_is_int =
      (match
         deduce_is_int_simple first.variant_blocks first.variant_immediates
           first.variant_is_int
       with
      | Some is_int -> Some ((first_id, is_int) :: [])
      | None -> None);
    parts_get_tag =
      (match
         deduce_get_tag_simple first.variant_blocks first.variant_get_tag
       with
      | Unknown -> None
      | Ok get_tag -> Some ((first_id, get_tag) :: [])
      | Bottom -> Some [])
  }

(** val add_variant_parts : Index.t -> variant_fields -> variant_parts ->
    variant_parts **)

let add_variant_parts other_id other acc =
  { parts_blocks = (other_id, other.variant_blocks) :: acc.parts_blocks;
    parts_immediates =
      (other_id, other.variant_immediates) :: acc.parts_immediates;
    parts_extensions =
      (other_id, other.variant_extensions_of) :: acc.parts_extensions;
    parts_is_unique = acc.parts_is_unique || other.variant_is_unique;
    parts_is_int =
      (match acc.parts_is_int with
      | Some is_int -> (
        match
          deduce_is_int_simple other.variant_blocks other.variant_immediates
            other.variant_is_int
        with
        | Some other_is_int -> Some ((other_id, other_is_int) :: is_int)
        | None -> None)
      | None -> None);
    parts_get_tag =
      (match acc.parts_get_tag with
      | Some get_tag -> (
        match
          deduce_get_tag_simple other.variant_blocks other.variant_get_tag
        with
        | Unknown -> None
        | Ok other_get_tag -> Some ((other_id, other_get_tag) :: get_tag)
        | Bottom -> Some get_tag)
      | None -> None)
  }

(** val read_mutable_block : head_of_kind_value_non_null -> Alloc_mode.t option
    **)

let read_mutable_block = function
  | Mutable_block alloc_mode -> Some alloc_mode
  | _ -> None

(** val read_boxed_number : boxable_number -> head_of_kind_value_non_null ->
    (flambda_type * Alloc_mode.t) option **)

let read_boxed_number k = function
  | Boxed_number (k', n, alloc_mode) ->
    if kind_eqb (unboxed_kind k) (unboxed_kind k')
    then Some (n, alloc_mode)
    else None
  | _ -> None

(** val read_closures : head_of_kind_value_non_null -> (row_like_for_closures *
    Alloc_mode.t) option **)

let read_closures = function
  | Closures (by_function_slot, alloc_mode) ->
    Some (by_function_slot, alloc_mode)
  | _ -> None

(** val read_string : head_of_kind_value_non_null -> coq_Z list list option **)

let read_string = function String strs -> Some strs | _ -> None

(** val extract_heads : (Expanded_type.head -> 'a1 option) -> (Index.t *
    Expanded_type.t) list -> (Index.t * 'a1) list option option **)

let rec extract_heads extract = function
  | [] -> Some (Some [])
  | p :: expandeds0 -> (
    let id2, expanded2 = p in
    match Expanded_type.descr expanded2 with
    | Unknown -> Some None
    | Ok head2 -> (
      match extract head2 with
      | Some head0 -> (
        match extract_heads extract expandeds0 with
        | Some heads -> Some (option_map (fun x -> (id2, head0) :: x) heads)
        | None -> None)
      | None -> None)
    | Bottom -> extract_heads extract expandeds0)

(** val alias_simples : (Index.t * flambda_type) list -> (Index.t * simple) list
    option **)

let rec alias_simples = function
  | [] -> Some []
  | p :: ts0 -> (
    let id, ty = p in
    match get_alias_opt ty with
    | Some simple0 -> (
      match alias_simples ts0 with
      | Some simples -> Some ((id, simple0) :: simples)
      | None -> None)
    | None -> None)

(** val fields_at : nat -> (Index.t * flambda_type list) list -> (Index.t *
    flambda_type) list option **)

let rec fields_at index = function
  | [] -> Some []
  | p :: fields0 -> (
    let id, fields_of_id = p in
    match nth_error fields_of_id index with
    | Some field -> (
      match fields_at index fields0 with
      | Some fields1 -> Some ((id, field) :: fields1)
      | None -> None)
    | None -> None)

type ('state, 'a) n_way_join_result = ('a Or_unknown.t * 'state) option

(** val map_join_result : ('a2 -> 'a3) -> ('a1, 'a2) n_way_join_result -> ('a1,
    'a3) n_way_join_result **)

let map_join_result f = function
  | Some p ->
    let v, env = p in
    Some (or_unknown_map f v, env)
  | None -> None

(** val n_way_join_unknown : ('a1 -> (Index.t * 'a2) list -> ('a1, 'a3)
    n_way_join_result) -> 'a1 -> (Index.t * 'a2 Or_unknown.t) list -> ('a1, 'a3)
    n_way_join_result **)

let n_way_join_unknown n_way_join_contents env or_unknowns =
  match known_contents [] or_unknowns with
  | Some contents -> n_way_join_contents env contents
  | None -> Some (Or_unknown.Unknown, env)

(** val n_way_join_head_of_kind_naked_number : 'a1 -> (coq_Z list * Index.t) ->
    (Index.t * coq_Z list) list -> ('a1, coq_Z list) n_way_join_result **)

let n_way_join_head_of_kind_naked_number env t1 ts =
  Some
    ( Or_unknown.Known
        (fold_left (fun t2 t3 -> numbers_union t2 (snd t3)) ts (fst t1)),
      env )

(** val n_way_join_relation_simples : ('a1 -> flambda_kind -> (Index.t * simple)
    list -> (simple Or_bottom.t * 'a1) option) -> 'a1 -> (Index.t * simple) list
    option -> (variable option * 'a1) option **)

let n_way_join_relation_simples n_way_join_simples env = function
  | Some simples -> (
    match
      n_way_join_simples env (Naked_number Kind_naked_immediate) simples
    with
    | Some p -> (
      let joined, env0 = p in
      match joined with
      | Or_bottom.Ok a -> (
        match a with Var var -> Some (Some var, env0) | _ -> Some (None, env0))
      | Or_bottom.Bottom -> Some (None, env0))
    | None -> None)
  | None -> Some (None, env)

(** val n_way_join_is_null : ('a1 -> flambda_kind -> (Index.t * simple) list ->
    (simple Or_bottom.t * 'a1) option) -> 'a1 -> (Index.t * head_of_kind_value)
    list -> (is_null * 'a1) option **)

let n_way_join_is_null n_way_join_simples env heads =
  match is_null_simples heads with
  | Some is_null_simples0 -> (
    match
      n_way_join_simples env (Naked_number Kind_naked_immediate)
        is_null_simples0
    with
    | Some p -> (
      let joined, env0 = p in
      match joined with
      | Or_bottom.Ok a -> (
        match a with
        | Var var -> Some (Maybe_null (Some var), env0)
        | Symbol _ -> None
        | Const c -> (
          match c with
          | Naked_immediate i ->
            Some ((if Z.eqb i Z0 then Not_null else Maybe_null None), env0)
          | _ -> Some (Maybe_null None, env0)))
      | Or_bottom.Bottom -> Some (Maybe_null None, env0))
    | None -> None)
  | None -> Some (Maybe_null None, env)

(** val join_naked_immediates : ('a1 -> Index.t -> Typing_env.t option) ->
    (Typing_env.t -> head_of_kind_naked_immediate ->
    head_of_kind_naked_immediate Or_bottom.t) -> 'a1 -> coq_Z list Or_unknown.t
    -> (Index.t * head_of_kind_naked_immediate) list -> coq_Z list Or_unknown.t
    option **)

let rec join_naked_immediates joined_env reduce_head_of_kind_naked_immediate env
    immediates = function
  | [] -> Some immediates
  | p :: heads0 -> (
    let id2, head2 = p in
    match joined_env env id2 with
    | Some tenv -> (
      match reduce_head_of_kind_naked_immediate tenv head2 with
      | Or_bottom.Ok head3 ->
        let immediates0 =
          match immediates with
          | Or_unknown.Known imms -> (
            match head3.naked_immediates with
            | Or_unknown.Known imms2 ->
              Or_unknown.Known (numbers_union imms imms2)
            | Or_unknown.Unknown -> Or_unknown.Unknown)
          | Or_unknown.Unknown -> Or_unknown.Unknown
        in
        join_naked_immediates joined_env reduce_head_of_kind_naked_immediate env
          immediates0 heads0
      | Or_bottom.Bottom ->
        join_naked_immediates joined_env reduce_head_of_kind_naked_immediate env
          immediates heads0)
    | None -> None)

(** val n_way_join_head_of_kind_naked_immediate : ('a1 -> Index.t ->
    Typing_env.t option) -> (Typing_env.t -> head_of_kind_naked_immediate ->
    head_of_kind_naked_immediate Or_bottom.t) -> 'a1 -> (Index.t *
    head_of_kind_naked_immediate) list -> ('a1, head_of_kind_naked_immediate)
    n_way_join_result **)

let n_way_join_head_of_kind_naked_immediate joined_env
    reduce_head_of_kind_naked_immediate env heads =
  match
    join_naked_immediates joined_env reduce_head_of_kind_naked_immediate env
      (Or_unknown.Known []) heads
  with
  | Some immediates -> (
    match immediates with
    | Or_unknown.Known imms ->
      if Keyed.is_empty imms
      then None
      else
        Some
          ( Or_unknown.Known
              { naked_immediates = Or_unknown.Known imms;
                inverse_relations = []
              },
            env )
    | Or_unknown.Unknown -> Some (Or_unknown.Unknown, env))
  | None -> None

(** val n_way_join_head_of_kind_naked_numbers : 'a1 -> (coq_Z list * Index.t) ->
    (Index.t * coq_Z list) list -> ('a1, coq_Z list) n_way_join_result **)

let n_way_join_head_of_kind_naked_numbers = n_way_join_head_of_kind_naked_number

(** val n_way_join_head_of_kind_rec_info : 'a1 -> (unit * Index.t) -> (Index.t *
    unit) list -> ('a1, unit) n_way_join_result **)

let n_way_join_head_of_kind_rec_info env t1 _ =
  Some (Or_unknown.Known (fst t1), env)

(** val n_way_join_head_of_kind_region : 'a1 -> (unit * Index.t) -> (Index.t *
    unit) list -> ('a1, unit) n_way_join_result **)

let n_way_join_head_of_kind_region env _ _ = Some (Or_unknown.Known (), env)

(** val n_way_join_env_extension : ('a1 -> (Index.t * env_extension) list ->
    (env_extension * 'a1) Or_bottom.t option) -> 'a1 -> (Index.t *
    env_extension) list -> (env_extension * 'a1) option **)

let n_way_join_env_extension join_env_n_way_join_env_extension env exts =
  match join_env_n_way_join_env_extension env exts with
  | Some joined -> (
    match joined with
    | Or_bottom.Ok a -> Some a
    | Or_bottom.Bottom -> Some (empty_env_extension, env))
  | None -> None

(** val generic_merge_map_known : ('a2 -> 'a2 -> bool) -> ('a4 -> 'a3) -> ('a1
    -> (Index.t * 'a3) list -> ('a3 * 'a1) Or_bottom.t option) -> 'a1 ->
    (Index.t * (('a2, 'a3) Keyed.finite_map * 'a4 Or_bottom.t)) list -> (('a2,
    'a3) Keyed.finite_map * 'a1) option **)

let generic_merge_map_known eqb0 of_other n_way_join0 env maps =
  match maps with
  | [] -> Some ([], env)
  | _ :: _ ->
    Keyed.filter_map_fold eqb0
      (fun _ values env0 ->
        match n_way_join0 env0 values with
        | Some joined -> (
          match joined with
          | Or_bottom.Ok a ->
            let value, env1 = a in
            Some (Some value, env1)
          | Or_bottom.Bottom -> Some (None, env0))
        | None -> None)
      (gather_known eqb0 of_other maps)
      env

(** val n_way_join_index : ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> 'a1) -> ('a2
    list -> 'a2 or_unknown_or_bottom) -> ('a1, 'a2) row_like_index list -> ('a1,
    'a2) row_like_index or_unknown_or_bottom **)

let n_way_join_index equal_index inter_index n_way_join_shape indexes =
  match n_way_join_shape (map (fun r -> r.index_shape) indexes) with
  | Unknown -> Unknown
  | Ok shape -> (
    match indexes with
    | [] -> Bottom
    | i1 :: indexes0 -> (
      let at_least =
       fun i1' ->
        Ok
          { index_domain =
              Row_like_index_domain.At_least
                (fold_left
                   (fun i1'0 i2 ->
                     match i2.index_domain with
                     | Row_like_index_domain.Known i2' -> inter_index i1'0 i2'
                     | Row_like_index_domain.At_least i2' ->
                       inter_index i1'0 i2')
                   indexes0 i1');
            index_shape = shape
          }
      in
      match i1.index_domain with
      | Row_like_index_domain.Known i1' ->
        if
          forallb
            (fun i2 ->
              match i2.index_domain with
              | Row_like_index_domain.Known i2' -> equal_index i1' i2'
              | Row_like_index_domain.At_least _ -> false)
            indexes0
        then Ok { index_domain = i1.index_domain; index_shape = shape }
        else at_least i1'
      | Row_like_index_domain.At_least i1' -> at_least i1'))
  | Bottom -> Bottom

(** val n_way_join_case : ('a1 -> (Index.t * env_extension) list ->
    (env_extension * 'a1) Or_bottom.t option) -> ('a1 -> 'a3 -> (Index.t * 'a4)
    list -> ('a4 * 'a1) option) -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a2 -> 'a2)
    -> ('a3 list -> 'a3 or_unknown_or_bottom) -> 'a1 -> (Index.t * ('a2, 'a3,
    'a4, env_extension) row_like_case) list -> (('a2, 'a3, 'a4, env_extension)
    row_like_case Or_unknown.t * 'a1) Or_bottom.t option **)

let n_way_join_case join_env_n_way_join_env_extension n_way_join_maps_to
    equal_index inter_index n_way_join_shape join_env cases =
  match
    n_way_join_index equal_index inter_index n_way_join_shape
      (map (fun case -> (snd case).case_index) cases)
  with
  | Unknown -> Some (Or_bottom.Ok (Or_unknown.Unknown, join_env))
  | Ok index -> (
    match
      n_way_join_maps_to join_env index.index_shape
        (map (fun case -> fst case, (snd case).case_maps_to) cases)
    with
    | Some p -> (
      let maps_to, join_env0 = p in
      match
        n_way_join_env_extension join_env_n_way_join_env_extension join_env0
          (map (fun case -> fst case, (snd case).case_env_extension) cases)
      with
      | Some p0 ->
        let env_extension0, join_env1 = p0 in
        Some
          (Or_bottom.Ok
             ( Or_unknown.Known
                 { case_maps_to = maps_to;
                   case_index = index;
                   case_env_extension = env_extension0
                 },
               join_env1 ))
      | None -> None)
    | None -> None)
  | Bottom -> Some Or_bottom.Bottom

(** val n_way_join_knowns : ('a1 -> (Index.t * env_extension) list ->
    (env_extension * 'a1) Or_bottom.t option) -> ('a1 -> 'a3 -> (Index.t * 'a4)
    list -> ('a4 * 'a1) option) -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a2 -> 'a2)
    -> ('a3 list -> 'a3 or_unknown_or_bottom) -> 'a1 -> (Index.t * ('a2, 'a3,
    'a4, env_extension) row_like_case Or_unknown.t) list -> (('a2, 'a3, 'a4,
    env_extension) row_like_case Or_unknown.t * 'a1) Or_bottom.t option **)

let n_way_join_knowns join_env_n_way_join_env_extension n_way_join_maps_to
    equal_index inter_index n_way_join_shape join_env cases =
  match all_known cases with
  | Some cases0 ->
    n_way_join_case join_env_n_way_join_env_extension n_way_join_maps_to
      equal_index inter_index n_way_join_shape join_env cases0
  | None -> Some (Or_bottom.Ok (Or_unknown.Unknown, join_env))

(** val n_way_join_row_like : ('a1 -> (Index.t * env_extension) list ->
    (env_extension * 'a1) Or_bottom.t option) -> ('a1 -> 'a3 -> (Index.t * 'a4)
    list -> ('a4 * 'a1) option) -> ('a2 -> 'a2 -> bool) -> ('a2 -> 'a2 -> 'a2)
    -> ('a3 list -> 'a3 or_unknown_or_bottom) -> (('a1 -> (Index.t * ('a2, 'a3,
    'a4, env_extension) row_like_case Or_unknown.t) list -> (('a2, 'a3, 'a4,
    env_extension) row_like_case Or_unknown.t * 'a1) Or_bottom.t option) -> 'a1
    -> (Index.t * ('a5 * ('a2, 'a3, 'a4, env_extension) row_like_case
    Or_bottom.t)) list -> ('a5 * 'a1) option) -> 'a1 -> (Index.t * ('a5 * ('a2,
    'a3, 'a4, env_extension) row_like_case Or_bottom.t)) list -> (Index.t *
    ('a2, 'a3, 'a4, env_extension) row_like_case Or_bottom.t) list -> ('a1, 'a5
    * ('a2, 'a3, 'a4, env_extension) row_like_case Or_bottom.t)
    n_way_join_result **)

let n_way_join_row_like join_env_n_way_join_env_extension n_way_join_maps_to
    equal_index inter_index n_way_join_shape merge_map_known join_env
    known_cases other =
  match
    merge_map_known
      (n_way_join_knowns join_env_n_way_join_env_extension n_way_join_maps_to
         equal_index inter_index n_way_join_shape)
      join_env known_cases
  with
  | Some p -> (
    let known, join_env0 = p in
    match
      n_way_join_case join_env_n_way_join_env_extension n_way_join_maps_to
        equal_index inter_index n_way_join_shape join_env0 (non_bottom [] other)
    with
    | Some other0 -> (
      match other0 with
      | Or_bottom.Ok a -> (
        let t0, join_env1 = a in
        match t0 with
        | Or_unknown.Known case ->
          Some (Or_unknown.Known (known, Or_bottom.Ok case), join_env1)
        | Or_unknown.Unknown -> Some (Or_unknown.Unknown, join_env1))
      | Or_bottom.Bottom ->
        Some (Or_unknown.Known (known, Or_bottom.Bottom), join_env0))
    | None -> None)
  | None -> None

(** val n_way_join_block_shape : (block_shape -> block_shape -> bool) ->
    block_shape list -> block_shape or_unknown_or_bottom **)

let n_way_join_block_shape block_shape_eqb = function
  | [] -> Bottom
  | shape1 :: shapes0 ->
    if forallb (block_shape_eqb shape1) shapes0 then Ok shape1 else Unknown

(** val n_way_join_generic_product : ('a1 -> (Index.t * flambda_type) list ->
    ('a1, flambda_type) n_way_join_result) -> 'a1 -> (Index.t * flambda_type
    finite_map) list -> (flambda_type finite_map * 'a1) option **)

let n_way_join_generic_product n_way_join_rec env indexed_products =
  match indexed_products with
  | [] -> Some ([], env)
  | _ :: _ ->
    Keyed.filter_map_fold Pos.eqb
      (fun _ tys env0 ->
        match n_way_join_rec env0 tys with
        | Some p -> (
          let joined, env1 = p in
          match joined with
          | Or_unknown.Known ty -> Some (Some ty, env1)
          | Or_unknown.Unknown -> Some (None, env1))
        | None -> None)
      (gather_components indexed_products)
      env

(** val n_way_join_function_slot_indexed_product : ('a1 -> (Index.t *
    flambda_type) list -> ('a1, flambda_type) n_way_join_result) -> 'a1 ->
    (Index.t * flambda_type finite_map) list -> (flambda_type finite_map * 'a1)
    option **)

let n_way_join_function_slot_indexed_product n_way_join_rec env
    function_slots_indexed =
  match
    n_way_join_generic_product n_way_join_rec env function_slots_indexed
  with
  | Some p ->
    let components, env0 = p in
    if
      Keyed.for_all_bindings_b Pos.eqb
        (fun _ ty -> kind_eqb (kind ty) Value)
        components
    then Some (components, env0)
    else None
  | None -> None

(** val n_way_join_value_slot_indexed_product : ('a1 -> (Index.t * flambda_type)
    list -> ('a1, flambda_type) n_way_join_result) -> 'a1 -> (Index.t *
    flambda_type finite_map) list -> (flambda_type finite_map * 'a1) option **)

let n_way_join_value_slot_indexed_product = n_way_join_generic_product

(** val fields_the_same : (flambda_type -> flambda_type -> bool) -> nat ->
    flambda_type list -> flambda_type list -> bool **)

let rec fields_the_same type_eqb length0 first_fields other_fields =
  match length0 with
  | O -> true
  | S length1 -> (
    match first_fields with
    | [] -> false
    | first_field :: first_fields0 -> (
      match other_fields with
      | [] -> false
      | other_field :: other_fields0 ->
        type_eqb other_field first_field
        && fields_the_same type_eqb length1 first_fields0 other_fields0))

(** val import_types : ('a1 -> flambda_type -> 'a1 option) -> 'a1 ->
    flambda_type list -> 'a1 option **)

let rec import_types import_type env = function
  | [] -> Some env
  | ty :: tys0 -> (
    match import_type env ty with
    | Some env0 -> import_types import_type env0 tys0
    | None -> None)

(** val join_fields : ('a1 -> (Index.t * flambda_type) list -> ('a1,
    flambda_type) n_way_join_result) -> 'a1 -> block_shape -> (Index.t *
    flambda_type list) list -> nat -> nat -> (flambda_type list * 'a1) option **)

let rec join_fields n_way_join_rec env shape fields index = function
  | O -> Some ([], env)
  | S count0 -> (
    match fields_at index fields with
    | Some tys -> (
      match n_way_join_rec env tys with
      | Some p -> (
        let joined, env0 = p in
        match
          match joined with
          | Or_unknown.Known ty -> Some ty
          | Or_unknown.Unknown -> unknown_from_shape shape index
        with
        | Some ty -> (
          match
            join_fields n_way_join_rec env0 shape fields (S index) count0
          with
          | Some p0 ->
            let tys0, env1 = p0 in
            Some (ty :: tys0, env1)
          | None -> None)
        | None -> None)
      | None -> None)
    | None -> None)

(** val n_way_join_int_indexed_product : ('a1 -> flambda_type -> 'a1 option) ->
    (flambda_type -> flambda_type -> bool) -> ('a1 -> (Index.t * flambda_type)
    list -> ('a1, flambda_type) n_way_join_result) -> 'a1 -> block_shape ->
    (Index.t * flambda_type list) list -> (flambda_type list * 'a1) option **)

let n_way_join_int_indexed_product import_type type_eqb n_way_join_rec env shape
    fields =
  match fields with
  | [] -> None
  | p :: other_fields ->
    let _, first_fields = p in
    let least_length =
      fold_left
        (fun least_length other_fields0 ->
          Nat.min least_length (length (snd other_fields0)))
        other_fields (length first_fields)
    in
    let all_the_same =
      forallb
        (fun other_fields0 ->
          fields_the_same type_eqb least_length first_fields (snd other_fields0))
        other_fields
    in
    if all_the_same
    then
      match
        find
          (fun fields_of_id -> Nat.eqb (length (snd fields_of_id)) least_length)
          fields
      with
      | Some p0 -> (
        let _, fields_of_id = p0 in
        match import_types import_type env fields_of_id with
        | Some env0 -> Some (fields_of_id, env0)
        | None -> None)
      | None -> None
    else join_fields n_way_join_rec env shape fields O least_length

(** val n_way_join_closures_entry : ('a1 -> (Index.t * flambda_type) list ->
    ('a1, flambda_type) n_way_join_result) -> 'a1 -> (Index.t * closures_entry)
    list -> (closures_entry * 'a1) option **)

let n_way_join_closures_entry n_way_join_rec env entries =
  let function_types =
    n_way_join_function_types
      (map
         (fun entry -> fst entry, closures_entry_function_types (snd entry))
         entries)
  in
  let closure_types =
    rev
      (map
         (fun entry -> fst entry, closures_entry_closure_types (snd entry))
         entries)
  in
  let value_slot_types =
    rev
      (map
         (fun entry -> fst entry, closures_entry_value_slot_types (snd entry))
         entries)
  in
  match
    n_way_join_function_slot_indexed_product n_way_join_rec env closure_types
  with
  | Some p -> (
    let closure_types0, env0 = p in
    match
      n_way_join_value_slot_indexed_product n_way_join_rec env0 value_slot_types
    with
    | Some p0 ->
      let value_slot_types0, env1 = p0 in
      Some
        ( Closures_entry (function_types, closure_types0, value_slot_types0),
          env1 )
    | None -> None)
  | None -> None

(** val n_way_join_row_like_for_blocks : ('a1 -> flambda_type -> 'a1 option) ->
    ('a1 -> (Index.t * env_extension) list -> (env_extension * 'a1) Or_bottom.t
    option) -> (flambda_type -> flambda_type -> bool) -> (block_shape ->
    block_shape -> bool) -> ('a1 -> (Index.t * flambda_type) list -> ('a1,
    flambda_type) n_way_join_result) -> 'a1 -> (Index.t * row_like_for_blocks)
    list -> ('a1, row_like_for_blocks) n_way_join_result **)

let n_way_join_row_like_for_blocks import_type join_env_n_way_join_env_extension
    type_eqb block_shape_eqb n_way_join_rec env row_likes =
  let split_or_bottom =
    fold_left
      (fun acc row_like ->
        let id = fst row_like in
        let row_like0 = snd row_like in
        if row_like_for_blocks_is_bottom row_like0
        then acc
        else
          match acc with
          | Or_bottom.Ok a ->
            let p, alloc_mode = a in
            let known, other = p in
            Or_bottom.Ok
              ( ( ( id,
                    ( row_like_known_tags row_like0,
                      row_like_other_tags row_like0 ) )
                  :: known,
                  (id, row_like_other_tags row_like0) :: other ),
                join_alloc_mode alloc_mode (row_like_alloc_mode row_like0) )
          | Or_bottom.Bottom ->
            Or_bottom.Ok
              ( ( ( id,
                    ( row_like_known_tags row_like0,
                      row_like_other_tags row_like0 ) )
                  :: [],
                  (id, row_like_other_tags row_like0) :: [] ),
                row_like_alloc_mode row_like0 ))
      row_likes Or_bottom.Bottom
  in
  match split_or_bottom with
  | Or_bottom.Ok a ->
    let p, alloc_mode = a in
    let known, other = p in
    map_join_result
      (fun joined -> Row_like_for_blocks (fst joined, snd joined, alloc_mode))
      (n_way_join_row_like join_env_n_way_join_env_extension
         (n_way_join_int_indexed_product import_type type_eqb n_way_join_rec)
         Nat.eqb Nat.min
         (n_way_join_block_shape block_shape_eqb)
         (generic_merge_map_known Z.eqb (fun x -> Or_unknown.Known x))
         env known other)
  | Or_bottom.Bottom -> Some (Or_unknown.Known row_like_for_blocks_bottom, env)

(** val n_way_join_row_like_for_closures : ('a1 -> (Index.t * env_extension)
    list -> (env_extension * 'a1) Or_bottom.t option) -> ('a1 -> (Index.t *
    flambda_type) list -> ('a1, flambda_type) n_way_join_result) -> 'a1 ->
    (Index.t * row_like_for_closures) list -> (row_like_for_closures * 'a1)
    option **)

let n_way_join_row_like_for_closures join_env_n_way_join_env_extension
    n_way_join_rec env closures =
  let known =
    rev
      (map
         (fun closures0 ->
           ( fst closures0,
             (row_like_known_closures (snd closures0), Or_bottom.Bottom) ))
         closures)
  in
  let merge_map_known =
   fun join_case env0 knowns ->
    generic_merge_map_known Pos.eqb
      (fun case -> case)
      (fun env1 cases ->
        let cases0 =
          map (fun case -> fst case, Or_unknown.Known (snd case)) cases
        in
        match join_case env1 cases0 with
        | Some joined -> (
          match joined with
          | Or_bottom.Ok a -> (
            let y, env2 = a in
            match y with
            | Or_unknown.Known case -> Some (Or_bottom.Ok (case, env2))
            | Or_unknown.Unknown -> None)
          | Or_bottom.Bottom -> Some Or_bottom.Bottom)
        | None -> None)
      env0 knowns
  in
  match
    n_way_join_row_like join_env_n_way_join_env_extension
      (fun env0 _ entries ->
        n_way_join_closures_entry n_way_join_rec env0 entries)
      set_of_closures_contents_equal set_of_closures_contents_inter
      (fun _ -> Ok ())
      merge_map_known env known []
  with
  | Some p -> (
    let joined, env0 = p in
    match joined with
    | Or_unknown.Known a -> (
      let known_closures, t0 = a in
      match t0 with
      | Or_bottom.Ok _ -> None
      | Or_bottom.Bottom -> Some (Row_like_for_closures known_closures, env0))
    | Or_unknown.Unknown -> None)
  | None -> None

(** val n_way_join_variant : ('a1 -> flambda_type -> 'a1 option) -> ('a1 ->
    (Index.t * env_extension) list -> (env_extension * 'a1) Or_bottom.t option)
    -> (flambda_type -> flambda_type -> bool) -> (block_shape -> block_shape ->
    bool) -> ('a1 -> (Index.t * flambda_type) list -> ('a1, flambda_type)
    n_way_join_result) -> 'a1 -> (Index.t * row_like_for_blocks Or_unknown.t)
    list -> (Index.t * flambda_type Or_unknown.t) list -> (Index.t *
    variant_extensions) list -> ('a1, (row_like_for_blocks Or_unknown.t *
    flambda_type Or_unknown.t) * variant_extensions) n_way_join_result **)

let n_way_join_variant import_type join_env_n_way_join_env_extension type_eqb
    block_shape_eqb n_way_join_rec env blocks imms extensions =
  match
    n_way_join_unknown
      (n_way_join_row_like_for_blocks import_type
         join_env_n_way_join_env_extension type_eqb block_shape_eqb
         n_way_join_rec)
      env blocks
  with
  | Some p -> (
    let blocks0, env0 = p in
    match n_way_join_unknown n_way_join_rec env0 imms with
    | Some p0 -> (
      let imms0, env1 = p0 in
      match gather_extensions [] [] extensions with
      | Some p1 -> (
        let when_immediates, when_blocks = p1 in
        match
          n_way_join_env_extension join_env_n_way_join_env_extension env1
            when_immediates
        with
        | Some p2 -> (
          let when_immediate, env2 = p2 in
          match
            n_way_join_env_extension join_env_n_way_join_env_extension env2
              when_blocks
          with
          | Some p3 -> (
            let when_block, env3 = p3 in
            if
              env_extension_is_empty when_immediate
              && env_extension_is_empty when_block
            then
              let p4 = env1, No_extensions in
              let env4, extensions0 = p4 in
              match blocks0 with
              | Or_unknown.Known _ ->
                Some (Or_unknown.Known ((blocks0, imms0), extensions0), env4)
              | Or_unknown.Unknown -> (
                match imms0 with
                | Or_unknown.Known _ ->
                  Some (Or_unknown.Known ((blocks0, imms0), extensions0), env4)
                | Or_unknown.Unknown -> (
                  match extensions0 with
                  | No_extensions -> Some (Or_unknown.Unknown, env4)
                  | Ext (_, _) ->
                    Some (Or_unknown.Known ((blocks0, imms0), extensions0), env4)
                  ))
            else
              let p4 = env3, Ext (when_immediate, when_block) in
              let env4, extensions0 = p4 in
              match blocks0 with
              | Or_unknown.Known _ ->
                Some (Or_unknown.Known ((blocks0, imms0), extensions0), env4)
              | Or_unknown.Unknown -> (
                match imms0 with
                | Or_unknown.Known _ ->
                  Some (Or_unknown.Known ((blocks0, imms0), extensions0), env4)
                | Or_unknown.Unknown -> (
                  match extensions0 with
                  | No_extensions -> Some (Or_unknown.Unknown, env4)
                  | Ext (_, _) ->
                    Some (Or_unknown.Known ((blocks0, imms0), extensions0), env4)
                  )))
          | None -> None)
        | None -> None)
      | None -> (
        let p1 = env1, No_extensions in
        let env2, extensions0 = p1 in
        match blocks0 with
        | Or_unknown.Known _ ->
          Some (Or_unknown.Known ((blocks0, imms0), extensions0), env2)
        | Or_unknown.Unknown -> (
          match imms0 with
          | Or_unknown.Known _ ->
            Some (Or_unknown.Known ((blocks0, imms0), extensions0), env2)
          | Or_unknown.Unknown -> (
            match extensions0 with
            | No_extensions -> Some (Or_unknown.Unknown, env2)
            | Ext (_, _) ->
              Some (Or_unknown.Known ((blocks0, imms0), extensions0), env2)))))
    | None -> None)
  | None -> None

(** val n_way_join_head_of_kind_value_non_null : ('a1 -> flambda_kind ->
    (Index.t * simple) list -> (simple Or_bottom.t * 'a1) option) -> ('a1 ->
    flambda_type -> 'a1 option) -> ('a1 -> (Index.t * env_extension) list ->
    (env_extension * 'a1) Or_bottom.t option) -> (flambda_type -> flambda_type
    -> bool) -> (block_shape -> block_shape -> bool) -> ('a1 -> (Index.t *
    flambda_type) list -> ('a1, flambda_type) n_way_join_result) -> 'a1 ->
    (Index.t * head_of_kind_value_non_null) list -> ('a1,
    head_of_kind_value_non_null) n_way_join_result **)

let n_way_join_head_of_kind_value_non_null n_way_join_simples import_type
    join_env_n_way_join_env_extension type_eqb block_shape_eqb n_way_join_rec
    env = function
  | [] -> None
  | p :: other_heads -> (
    let first_id, first_head = p in
    match first_head with
    | Variant (is_int, immediates, get_tag, blocks, extensions, is_unique) -> (
      let first =
        { variant_is_int = is_int;
          variant_immediates = immediates;
          variant_get_tag = get_tag;
          variant_blocks = blocks;
          variant_extensions_of = extensions;
          variant_is_unique = is_unique
        }
      in
      match
        gather_heads read_variant add_variant_parts other_heads
          (first_variant_parts first_id first)
      with
      | Some parts -> (
        match
          n_way_join_relation_simples n_way_join_simples env parts.parts_is_int
        with
        | Some p0 -> (
          let is_int0, env0 = p0 in
          match
            n_way_join_relation_simples n_way_join_simples env0
              parts.parts_get_tag
          with
          | Some p1 ->
            let get_tag0, env1 = p1 in
            map_join_result
              (fun joined ->
                Variant
                  ( is_int0,
                    snd (fst joined),
                    get_tag0,
                    fst (fst joined),
                    snd joined,
                    parts.parts_is_unique ))
              (n_way_join_variant import_type join_env_n_way_join_env_extension
                 type_eqb block_shape_eqb n_way_join_rec env1 parts.parts_blocks
                 parts.parts_immediates parts.parts_extensions)
          | None -> None)
        | None -> None)
      | None -> Some (Or_unknown.Unknown, env))
    | Mutable_block alloc_mode -> (
      match
        gather_heads read_mutable_block
          (fun _ other_alloc_mode alloc_mode0 ->
            join_alloc_mode alloc_mode0 other_alloc_mode)
          other_heads alloc_mode
      with
      | Some alloc_mode0 ->
        Some (Or_unknown.Known (Mutable_block alloc_mode0), env)
      | None -> Some (Or_unknown.Unknown, env))
    | Boxed_number (k, n, alloc_mode) -> (
      match
        gather_heads (read_boxed_number k)
          (fun other_id other acc ->
            ( (other_id, fst other) :: fst acc,
              join_alloc_mode (snd acc) (snd other) ))
          other_heads
          ((first_id, n) :: [], alloc_mode)
      with
      | Some p0 ->
        let ns, alloc_mode0 = p0 in
        map_join_result
          (fun n0 -> Boxed_number (k, n0, alloc_mode0))
          (n_way_join_rec env ns)
      | None -> Some (Or_unknown.Unknown, env))
    | Closures (by_function_slot, alloc_mode) -> (
      match
        gather_heads read_closures
          (fun other_id other acc ->
            ( (other_id, fst other) :: fst acc,
              join_alloc_mode (snd acc) (snd other) ))
          other_heads
          ((first_id, by_function_slot) :: [], alloc_mode)
      with
      | Some p0 -> (
        let function_slots, alloc_mode0 = p0 in
        match
          n_way_join_row_like_for_closures join_env_n_way_join_env_extension
            n_way_join_rec env function_slots
        with
        | Some p1 ->
          let by_function_slot0, env0 = p1 in
          Some
            (Or_unknown.Known (Closures (by_function_slot0, alloc_mode0)), env0)
        | None -> None)
      | None -> Some (Or_unknown.Unknown, env))
    | String strs -> (
      match
        gather_heads read_string (fun _ -> strings_union) other_heads strs
      with
      | Some all_strs -> Some (Or_unknown.Known (String all_strs), env)
      | None -> Some (Or_unknown.Unknown, env)))

(** val n_way_join_head_of_kind_value : ('a1 -> flambda_kind -> (Index.t *
    simple) list -> (simple Or_bottom.t * 'a1) option) -> ('a1 -> flambda_type
    -> 'a1 option) -> ('a1 -> (Index.t * env_extension) list -> (env_extension *
    'a1) Or_bottom.t option) -> (flambda_type -> flambda_type -> bool) ->
    (block_shape -> block_shape -> bool) -> ('a1 -> (Index.t * flambda_type)
    list -> ('a1, flambda_type) n_way_join_result) -> 'a1 -> (Index.t *
    head_of_kind_value) list -> ('a1, head_of_kind_value) n_way_join_result **)

let n_way_join_head_of_kind_value n_way_join_simples import_type
    join_env_n_way_join_env_extension type_eqb block_shape_eqb n_way_join_rec
    env heads =
  match n_way_join_is_null n_way_join_simples env heads with
  | Some p -> (
    let is_null0, env0 = p in
    match non_null_heads [] heads with
    | Some non_nulls -> (
      match non_nulls with
      | [] -> (
        let p0 = Bottom, env0 in
        let non_null, env1 = p0 in
        match non_null with
        | Unknown -> (
          match is_null0 with
          | Not_null ->
            Some
              (Or_unknown.Known (Head_of_kind_value (non_null, is_null0)), env1)
          | Maybe_null is_null1 -> (
            match is_null1 with
            | Some _ ->
              Some
                ( Or_unknown.Known (Head_of_kind_value (non_null, is_null0)),
                  env1 )
            | None -> Some (Or_unknown.Unknown, env1)))
        | _ ->
          Some (Or_unknown.Known (Head_of_kind_value (non_null, is_null0)), env1)
        )
      | _ :: _ -> (
        match
          n_way_join_head_of_kind_value_non_null n_way_join_simples import_type
            join_env_n_way_join_env_extension type_eqb block_shape_eqb
            n_way_join_rec env0 non_nulls
        with
        | Some p0 -> (
          let joined, env1 = p0 in
          match joined with
          | Or_unknown.Known head0 -> (
            let p1 = Ok head0, env1 in
            let non_null, env2 = p1 in
            match non_null with
            | Unknown -> (
              match is_null0 with
              | Not_null ->
                Some
                  ( Or_unknown.Known (Head_of_kind_value (non_null, is_null0)),
                    env2 )
              | Maybe_null is_null1 -> (
                match is_null1 with
                | Some _ ->
                  Some
                    ( Or_unknown.Known (Head_of_kind_value (non_null, is_null0)),
                      env2 )
                | None -> Some (Or_unknown.Unknown, env2)))
            | _ ->
              Some
                ( Or_unknown.Known (Head_of_kind_value (non_null, is_null0)),
                  env2 ))
          | Or_unknown.Unknown -> (
            let p1 = Unknown, env1 in
            let non_null, env2 = p1 in
            match non_null with
            | Unknown -> (
              match is_null0 with
              | Not_null ->
                Some
                  ( Or_unknown.Known (Head_of_kind_value (non_null, is_null0)),
                    env2 )
              | Maybe_null is_null1 -> (
                match is_null1 with
                | Some _ ->
                  Some
                    ( Or_unknown.Known (Head_of_kind_value (non_null, is_null0)),
                      env2 )
                | None -> Some (Or_unknown.Unknown, env2)))
            | _ ->
              Some
                ( Or_unknown.Known (Head_of_kind_value (non_null, is_null0)),
                  env2 )))
        | None -> None))
    | None -> (
      let p0 = Unknown, env0 in
      let non_null, env1 = p0 in
      match non_null with
      | Unknown -> (
        match is_null0 with
        | Not_null ->
          Some (Or_unknown.Known (Head_of_kind_value (non_null, is_null0)), env1)
        | Maybe_null is_null1 -> (
          match is_null1 with
          | Some _ ->
            Some
              (Or_unknown.Known (Head_of_kind_value (non_null, is_null0)), env1)
          | None -> Some (Or_unknown.Unknown, env1)))
      | _ ->
        Some (Or_unknown.Known (Head_of_kind_value (non_null, is_null0)), env1))
    )
  | None -> None

(** val n_way_join_expanded_head : ('a1 -> Index.t -> Typing_env.t option) ->
    ('a1 -> flambda_kind -> (Index.t * simple) list -> (simple Or_bottom.t *
    'a1) option) -> ('a1 -> flambda_type -> 'a1 option) -> ('a1 -> (Index.t *
    env_extension) list -> (env_extension * 'a1) Or_bottom.t option) ->
    (Typing_env.t -> head_of_kind_naked_immediate ->
    head_of_kind_naked_immediate Or_bottom.t) -> (flambda_type -> flambda_type
    -> bool) -> (block_shape -> block_shape -> bool) -> ('a1 -> (Index.t *
    flambda_type) list -> ('a1, flambda_type) n_way_join_result) -> 'a1 ->
    flambda_kind -> (Index.t * Expanded_type.t) list -> ('a1, Expanded_type.t)
    n_way_join_result **)

let rec n_way_join_expanded_head joined_env n_way_join_simples import_type
    join_env_n_way_join_env_extension reduce_head_of_kind_naked_immediate
    type_eqb block_shape_eqb n_way_join_rec env kind0 = function
  | [] -> Some (Or_unknown.Known (Expanded_type.create_bottom kind0), env)
  | p :: expandeds0 -> (
    let id1, expanded1 = p in
    match Expanded_type.descr expanded1 with
    | Unknown ->
      Some (Or_unknown.Known (Expanded_type.create_unknown kind0), env)
    | Ok descr1 -> (
      match
        match descr1 with
        | Expanded_type.Head_value head1 -> (
          match
            extract_heads
              (fun head0 ->
                match head0 with
                | Expanded_type.Head_value head2 -> Some head2
                | _ -> None)
              expandeds0
          with
          | Some heads -> (
            match heads with
            | Some heads0 ->
              map_join_result Expanded_type.create_value
                (n_way_join_head_of_kind_value n_way_join_simples import_type
                   join_env_n_way_join_env_extension type_eqb block_shape_eqb
                   n_way_join_rec env ((id1, head1) :: heads0))
            | None -> Some (Or_unknown.Unknown, env))
          | None -> None)
        | Expanded_type.Head_naked_immediate head1 -> (
          match
            extract_heads
              (fun head0 ->
                match head0 with
                | Expanded_type.Head_value _ -> None
                | Expanded_type.Head_naked_immediate head2 -> Some head2
                | _ -> None)
              expandeds0
          with
          | Some heads -> (
            match heads with
            | Some heads0 ->
              map_join_result Expanded_type.create_naked_immediate
                (n_way_join_head_of_kind_naked_immediate joined_env
                   reduce_head_of_kind_naked_immediate env
                   ((id1, head1) :: heads0))
            | None -> Some (Or_unknown.Unknown, env))
          | None -> None)
        | Expanded_type.Head_naked_number (k, head1) -> (
          match
            extract_heads
              (fun head0 ->
                match head0 with
                | Expanded_type.Head_value _ -> None
                | Expanded_type.Head_naked_immediate _ -> None
                | Expanded_type.Head_naked_number (k', head2) ->
                  if kind_eqb (Naked_number k) (Naked_number k')
                  then Some head2
                  else None
                | _ -> None)
              expandeds0
          with
          | Some heads -> (
            match heads with
            | Some heads0 ->
              map_join_result
                (Expanded_type.create_naked_number k)
                (n_way_join_head_of_kind_naked_numbers env (head1, id1) heads0)
            | None -> Some (Or_unknown.Unknown, env))
          | None -> None)
        | Expanded_type.Head_rec_info head1 -> (
          match
            extract_heads
              (fun head0 ->
                match head0 with
                | Expanded_type.Head_value _ -> None
                | Expanded_type.Head_naked_immediate _ -> None
                | Expanded_type.Head_naked_number (_, _) -> None
                | Expanded_type.Head_rec_info head2 -> Some head2
                | Expanded_type.Head_region _ -> None)
              expandeds0
          with
          | Some heads -> (
            match heads with
            | Some heads0 ->
              map_join_result Expanded_type.create_rec_info
                (n_way_join_head_of_kind_rec_info env (head1, id1) heads0)
            | None -> Some (Or_unknown.Unknown, env))
          | None -> None)
        | Expanded_type.Head_region head1 -> (
          match
            extract_heads
              (fun head0 ->
                match head0 with
                | Expanded_type.Head_value _ -> None
                | Expanded_type.Head_naked_immediate _ -> None
                | Expanded_type.Head_naked_number (_, _) -> None
                | Expanded_type.Head_rec_info _ -> None
                | Expanded_type.Head_region head2 -> Some head2)
              expandeds0
          with
          | Some heads -> (
            match heads with
            | Some heads0 ->
              map_join_result Expanded_type.create_region
                (n_way_join_head_of_kind_region env (head1, id1) heads0)
            | None -> Some (Or_unknown.Unknown, env))
          | None -> None)
      with
      | Some p0 -> (
        let expanded_or_unknown, env0 = p0 in
        match expanded_or_unknown with
        | Or_unknown.Known expanded -> Some (Or_unknown.Known expanded, env0)
        | Or_unknown.Unknown ->
          Some (Or_unknown.Known (Expanded_type.unknown_like expanded1), env0))
      | None -> None)
    | Bottom ->
      n_way_join_expanded_head joined_env n_way_join_simples import_type
        join_env_n_way_join_env_extension reduce_head_of_kind_naked_immediate
        type_eqb block_shape_eqb n_way_join_rec env kind0 expandeds0)

(** val expand_heads : ('a1 -> Index.t -> Typing_env.t option) -> (Typing_env.t
    -> flambda_type -> Expanded_type.t option) -> 'a1 -> (Index.t *
    flambda_type) list -> (Index.t * Expanded_type.t) list option **)

let rec expand_heads joined_env expand_head env = function
  | [] -> Some []
  | p :: ts0 -> (
    let id, ty = p in
    match joined_env env id with
    | Some tenv -> (
      match expand_head tenv ty with
      | Some expanded -> (
        match expand_heads joined_env expand_head env ts0 with
        | Some expandeds -> Some ((id, expanded) :: expandeds)
        | None -> None)
      | None -> None)
    | None -> None)

(** val n_way_join_body : ('a1 -> Index.t -> Typing_env.t option) -> ('a1 ->
    flambda_kind -> (Index.t * simple) list -> (simple Or_bottom.t * 'a1)
    option) -> ('a1 -> flambda_type -> 'a1 option) -> ('a1 -> (Index.t *
    env_extension) list -> (env_extension * 'a1) Or_bottom.t option) ->
    (Typing_env.t -> flambda_type -> Expanded_type.t option) -> (Typing_env.t ->
    head_of_kind_naked_immediate -> head_of_kind_naked_immediate Or_bottom.t) ->
    (flambda_type -> flambda_type -> bool) -> (block_shape -> block_shape ->
    bool) -> ('a1 -> (Index.t * flambda_type) list -> ('a1, flambda_type)
    n_way_join_result) -> 'a1 -> (Index.t * flambda_type) list -> ('a1,
    flambda_type) n_way_join_result **)

let n_way_join_body joined_env n_way_join_simples import_type
    join_env_n_way_join_env_extension expand_head
    reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb n_way_join_rec
    env ts =
  match ts with
  | [] -> None
  | p :: others -> (
    let _, t1 = p in
    let kind0 = kind t1 in
    if negb (forallb (fun t0 -> kind_eqb kind0 (kind (snd t0))) others)
    then None
    else
      let ts0 = filter (fun t0 -> negb (is_obviously_bottom (snd t0))) ts in
      match alias_simples ts0 with
      | Some canonical_simples -> (
        match n_way_join_simples env kind0 canonical_simples with
        | Some p0 -> (
          let joined, env0 = p0 in
          match joined with
          | Or_bottom.Ok simple0 ->
            Some (Or_unknown.Known (alias_type_of kind0 simple0), env0)
          | Or_bottom.Bottom -> Some (Or_unknown.Known (bottom kind0), env0))
        | None -> None)
      | None -> (
        match expand_heads joined_env expand_head env ts0 with
        | Some expandeds ->
          map_join_result Expanded_type.to_type
            (n_way_join_expanded_head joined_env n_way_join_simples import_type
               join_env_n_way_join_env_extension
               reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb
               n_way_join_rec env kind0 expandeds)
        | None -> None))

(** val n_way_join : ('a1 -> Index.t -> Typing_env.t option) -> ('a1 ->
    flambda_kind -> (Index.t * simple) list -> (simple Or_bottom.t * 'a1)
    option) -> ('a1 -> flambda_type -> 'a1 option) -> ('a1 -> (Index.t *
    env_extension) list -> (env_extension * 'a1) Or_bottom.t option) ->
    (Typing_env.t -> flambda_type -> Expanded_type.t option) -> (Typing_env.t ->
    head_of_kind_naked_immediate -> head_of_kind_naked_immediate Or_bottom.t) ->
    (flambda_type -> flambda_type -> bool) -> (block_shape -> block_shape ->
    bool) -> nat -> 'a1 -> (Index.t * flambda_type) list -> ('a1, flambda_type)
    n_way_join_result **)

let rec n_way_join joined_env n_way_join_simples import_type
    join_env_n_way_join_env_extension expand_head
    reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb = function
  | O -> fun _ _ -> None
  | S fuel0 ->
    n_way_join_body joined_env n_way_join_simples import_type
      join_env_n_way_join_env_extension expand_head
      reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb
      (n_way_join joined_env n_way_join_simples import_type
         join_env_n_way_join_env_extension expand_head
         reduce_head_of_kind_naked_immediate type_eqb block_shape_eqb fuel0)
