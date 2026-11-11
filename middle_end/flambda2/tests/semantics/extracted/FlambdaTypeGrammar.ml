open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

type name =
  | Name_var of variable
  | Name_symbol of symbol

(** val simple_of_name : name -> simple **)

let simple_of_name = function Name_var x -> Var x | Name_symbol s -> Symbol s

(** val name_eqb : name -> name -> bool **)

let name_eqb n n' =
  match n with
  | Name_var x -> (
    match n' with Name_var x' -> Pos.eqb x x' | Name_symbol _ -> false)
  | Name_symbol s -> (
    match n' with Name_var _ -> false | Name_symbol s' -> Pos.eqb s s')

module Or_unknown = struct
  type 'a t =
    | Known of 'a
    | Unknown
end

module Or_bottom = struct
  type 'a t =
    | Ok of 'a
    | Bottom
end

type 'a or_unknown_or_bottom =
  | Unknown
  | Ok of 'a
  | Bottom

type 'head descr =
  | No_alias of 'head
  | Equals of simple

type 'head type_descr = 'head descr or_unknown_or_bottom

module Alloc_mode = struct
  type t =
    | Heap
    | Local
    | Heap_or_local
end

type is_null =
  | Not_null
  | Maybe_null of variable option

module Relation = struct
  type t =
    | Is_null
    | Is_int
    | Get_tag

  (** val of_const : t -> const -> coq_Z Or_bottom.t **)

  let of_const relation c =
    match relation with
    | Is_null -> (
      match c with Null -> Or_bottom.Ok (Zpos Coq_xH) | _ -> Or_bottom.Ok Z0)
    | Is_int -> (
      match c with Null -> Or_bottom.Ok Z0 | _ -> Or_bottom.Ok (Zpos Coq_xH))
    | Get_tag -> Or_bottom.Bottom
end

type head_of_kind_naked_immediate =
  { naked_immediates : coq_Z list Or_unknown.t;
    inverse_relations : (Relation.t * name) list
  }

type scannable_block_shape =
  | Value_only
  | Mixed_record of nat * naked_number_kind list

type block_shape =
  | Scannable of scannable_block_shape
  | Float_record

(** val no_scan_tag : coq_Z **)

let no_scan_tag =
  Zpos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))))

(** val double_array_tag : coq_Z **)

let double_array_tag =
  Zpos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))))

module Row_like_index_domain = struct
  type 'lattice t =
    | Known of 'lattice
    | At_least of 'lattice
end

type ('lattice, 'shape) row_like_index =
  { index_domain : 'lattice Row_like_index_domain.t;
    index_shape : 'shape
  }

type ('lattice, 'shape, 'maps_to, 'extension) row_like_case =
  { case_maps_to : 'maps_to;
    case_index : ('lattice, 'shape) row_like_index;
    case_env_extension : 'extension
  }

type set_of_closures_contents =
  { contents_closures : function_slot list;
    contents_value_slots : value_slot list
  }

type function_type = { function_type_code_id : code_id }

type flambda_type =
  | Type_value of head_of_kind_value type_descr
  | Type_naked_immediate of head_of_kind_naked_immediate type_descr
  | Type_naked_number of naked_number_kind * coq_Z list type_descr
  | Type_rec_info of unit type_descr
  | Type_region of unit type_descr

and head_of_kind_value =
  | Head_of_kind_value of
      head_of_kind_value_non_null or_unknown_or_bottom * is_null

and head_of_kind_value_non_null =
  | Variant of
      variable option
      * flambda_type Or_unknown.t
      * variable option
      * row_like_for_blocks Or_unknown.t
      * variant_extensions
      * bool
  | Mutable_block of Alloc_mode.t
  | Boxed_number of boxable_number * flambda_type * Alloc_mode.t
  | Closures of row_like_for_closures * Alloc_mode.t
  | String of coq_Z list list

and row_like_for_blocks =
  | Row_like_for_blocks of
      ( coq_Z,
        (nat, block_shape, flambda_type list, env_extension) row_like_case
        Or_unknown.t )
      Keyed.finite_map
      * (nat, block_shape, flambda_type list, env_extension) row_like_case
        Or_bottom.t
      * Alloc_mode.t

and row_like_for_closures =
  | Row_like_for_closures of
      ( set_of_closures_contents,
        unit,
        closures_entry,
        env_extension )
      row_like_case
      finite_map

and closures_entry =
  | Closures_entry of
      function_type Or_unknown.t finite_map
      * flambda_type finite_map
      * flambda_type finite_map

and env_extension = Env_extension of (name, flambda_type) Keyed.finite_map

and variant_extensions =
  | No_extensions
  | Ext of env_extension * env_extension

type row_like_block_case =
  (nat, block_shape, flambda_type list, env_extension) row_like_case

type row_like_closures_case =
  (set_of_closures_contents, unit, closures_entry, env_extension) row_like_case

(** val kind : flambda_type -> flambda_kind **)

let kind = function
  | Type_value _ -> Value
  | Type_naked_immediate _ -> Naked_number Kind_naked_immediate
  | Type_naked_number (k, _) -> Naked_number k
  | Type_rec_info _ -> Rec_info
  | Type_region _ -> Region

(** val field_kinds : block_shape -> nat -> flambda_kind list **)

let field_kinds shape size =
  match shape with
  | Scannable shape0 -> (
    match shape0 with
    | Value_only -> repeat Value size
    | Mixed_record (value_prefix_size, flat_suffix) ->
      app
        (repeat Value value_prefix_size)
        (map (fun x -> Naked_number x) flat_suffix))
  | Float_record -> repeat (Naked_number Kind_naked_float) size

(** val unknown : flambda_kind -> flambda_type **)

let unknown = function
  | Value -> Type_value Unknown
  | Naked_number k0 -> (
    match k0 with
    | Kind_naked_immediate -> Type_naked_immediate Unknown
    | _ -> Type_naked_number (k0, Unknown))
  | Region -> Type_region Unknown
  | Rec_info -> Type_rec_info Unknown

(** val bottom : flambda_kind -> flambda_type **)

let bottom = function
  | Value -> Type_value Bottom
  | Naked_number k0 -> (
    match k0 with
    | Kind_naked_immediate -> Type_naked_immediate Bottom
    | _ -> Type_naked_number (k0, Bottom))
  | Region -> Type_region Bottom
  | Rec_info -> Type_rec_info Bottom

(** val alias_type_of : flambda_kind -> simple -> flambda_type **)

let alias_type_of k s =
  match k with
  | Value -> Type_value (Ok (Equals s))
  | Naked_number k0 -> (
    match k0 with
    | Kind_naked_immediate -> Type_naked_immediate (Ok (Equals s))
    | _ -> Type_naked_number (k0, Ok (Equals s)))
  | Region -> Type_region (Ok (Equals s))
  | Rec_info -> Type_rec_info (Ok (Equals s))

(** val get_alias_opt : flambda_type -> simple option **)

let get_alias_opt t0 =
  let of_descr =
   fun ty ->
    match ty with
    | Unknown -> None
    | Ok a -> ( match a with No_alias _ -> None | Equals s -> Some s)
    | Bottom -> None
  in
  match t0 with
  | Type_value ty -> of_descr ty
  | Type_naked_immediate ty -> of_descr ty
  | Type_naked_number (_, ty) -> of_descr ty
  | Type_rec_info ty -> of_descr ty
  | Type_region ty -> of_descr ty

(** val is_obviously_bottom : flambda_type -> bool **)

let is_obviously_bottom t0 =
  let of_descr = fun ty -> match ty with Bottom -> true | _ -> false in
  match t0 with
  | Type_value ty -> of_descr ty
  | Type_naked_immediate ty -> of_descr ty
  | Type_naked_number (_, ty) -> of_descr ty
  | Type_rec_info ty -> of_descr ty
  | Type_region ty -> of_descr ty

(** val is_obviously_unknown : flambda_type -> bool **)

let is_obviously_unknown t0 =
  let of_descr = fun ty -> match ty with Unknown -> true | _ -> false in
  match t0 with
  | Type_value ty -> of_descr ty
  | Type_naked_immediate ty -> of_descr ty
  | Type_naked_number (_, ty) -> of_descr ty
  | Type_rec_info ty -> of_descr ty
  | Type_region ty -> of_descr ty

(** val this_const : const -> flambda_type **)

let this_const c = alias_type_of (kind_of_const c) (Const c)

(** val this_tagged_immediate : coq_Z -> flambda_type **)

let this_tagged_immediate i = this_const (Tagged_immediate i)

(** val this_naked_immediate : coq_Z -> flambda_type **)

let this_naked_immediate i = this_const (Naked_immediate i)

(** val null : flambda_type **)

let null =
  Type_value (Ok (No_alias (Head_of_kind_value (Bottom, Maybe_null None))))

(** val any_non_null_value : flambda_type **)

let any_non_null_value =
  Type_value (Ok (No_alias (Head_of_kind_value (Unknown, Not_null))))

(** val type_for_const : const -> flambda_type **)

let type_for_const c =
  match c with Null -> null | Poison k -> unknown k | _ -> this_const c

(** val non_null_value : head_of_kind_value_non_null -> flambda_type **)

let non_null_value head =
  Type_value (Ok (No_alias (Head_of_kind_value (Ok head, Not_null))))

(** val create_variant : bool -> flambda_type Or_unknown.t ->
    row_like_for_blocks Or_unknown.t -> variant_extensions -> flambda_type **)

let create_variant is_unique immediates blocks extensions =
  non_null_value
    (Variant (None, immediates, None, blocks, extensions, is_unique))

(** val mutable_block : Alloc_mode.t -> flambda_type **)

let mutable_block alloc_mode = non_null_value (Mutable_block alloc_mode)

(** val create_closures : Alloc_mode.t -> row_like_for_closures -> flambda_type
    **)

let create_closures alloc_mode by_function_slot =
  non_null_value (Closures (by_function_slot, alloc_mode))

(** val box_number : boxable_number -> flambda_type -> Alloc_mode.t ->
    flambda_type **)

let box_number k contents alloc_mode =
  non_null_value (Boxed_number (k, contents, alloc_mode))

(** val this_immutable_string : coq_Z list -> flambda_type **)

let this_immutable_string bytes = non_null_value (String (bytes :: []))

(** val these_naked_immediates : coq_Z list -> flambda_type **)

let these_naked_immediates imms =
  match imms with
  | [] -> bottom (Naked_number Kind_naked_immediate)
  | i :: l -> (
    match l with
    | [] -> this_naked_immediate i
    | _ :: _ ->
      Type_naked_immediate
        (Ok
           (No_alias
              { naked_immediates = Or_unknown.Known imms;
                inverse_relations = []
              })))

(** val empty_env_extension : env_extension **)

let empty_env_extension = Env_extension []

(** val row_like_for_blocks_bottom : row_like_for_blocks **)

let row_like_for_blocks_bottom =
  Row_like_for_blocks ([], Or_bottom.Bottom, Alloc_mode.Heap_or_local)

(** val row_like_for_blocks_is_bottom : row_like_for_blocks -> bool **)

let row_like_for_blocks_is_bottom = function
  | Row_like_for_blocks (known_tags, other_tags, _) -> (
    match known_tags with
    | [] -> (
      match other_tags with Or_bottom.Ok _ -> false | Or_bottom.Bottom -> true)
    | _ :: _ -> false)

(** val row_like_for_blocks_create_exactly : coq_Z -> nat -> block_shape ->
    flambda_type list -> Alloc_mode.t -> row_like_for_blocks **)

let row_like_for_blocks_create_exactly tag size shape maps_to alloc_mode =
  Row_like_for_blocks
    ( ( tag,
        Or_unknown.Known
          { case_maps_to = maps_to;
            case_index =
              { index_domain = Row_like_index_domain.Known size;
                index_shape = shape
              };
            case_env_extension = empty_env_extension
          } )
      :: [],
      Or_bottom.Bottom,
      alloc_mode )

(** val row_like_for_blocks_create_at_least : coq_Z -> nat -> block_shape ->
    flambda_type list -> Alloc_mode.t -> row_like_for_blocks **)

let row_like_for_blocks_create_at_least tag size shape maps_to alloc_mode =
  Row_like_for_blocks
    ( ( tag,
        Or_unknown.Known
          { case_maps_to = maps_to;
            case_index =
              { index_domain = Row_like_index_domain.At_least size;
                index_shape = shape
              };
            case_env_extension = empty_env_extension
          } )
      :: [],
      Or_bottom.Bottom,
      alloc_mode )

(** val row_like_for_blocks_create_at_least_unknown_tag : nat -> block_shape ->
    flambda_type list -> Alloc_mode.t -> row_like_for_blocks **)

let row_like_for_blocks_create_at_least_unknown_tag size shape maps_to
    alloc_mode =
  Row_like_for_blocks
    ( [],
      Or_bottom.Ok
        { case_maps_to = maps_to;
          case_index =
            { index_domain = Row_like_index_domain.At_least size;
              index_shape = shape
            };
          case_env_extension = empty_env_extension
        },
      alloc_mode )

(** val tag_immediate : flambda_type -> flambda_type **)

let tag_immediate t0 =
  create_variant false (Or_unknown.Known t0)
    (Or_unknown.Known row_like_for_blocks_bottom) No_extensions

(** val any_tagged_immediate : flambda_type **)

let any_tagged_immediate =
  create_variant false Or_unknown.Unknown
    (Or_unknown.Known row_like_for_blocks_bottom) No_extensions

(** val these_tagged_immediates : coq_Z list -> flambda_type **)

let these_tagged_immediates imms =
  match imms with
  | [] -> bottom Value
  | i :: l -> (
    match l with
    | [] -> this_tagged_immediate i
    | _ :: _ -> tag_immediate (these_naked_immediates imms))

(** val any_block : flambda_type **)

let any_block =
  create_variant false
    (Or_unknown.Known (bottom (Naked_number Kind_naked_immediate)))
    Or_unknown.Unknown No_extensions

(** val blocks_with_these_tags : coq_Z list -> Alloc_mode.t -> flambda_type **)

let blocks_with_these_tags tags alloc_mode =
  create_variant false
    (Or_unknown.Known (bottom (Naked_number Kind_naked_immediate)))
    (Or_unknown.Known
       (Row_like_for_blocks
          ( map (fun tag -> tag, Or_unknown.Unknown) tags,
            Or_bottom.Bottom,
            alloc_mode )))
    No_extensions

(** val immutable_block : bool -> coq_Z -> block_shape -> Alloc_mode.t ->
    flambda_type list -> flambda_type **)

let immutable_block is_unique tag shape alloc_mode fields =
  create_variant is_unique
    (Or_unknown.Known (bottom (Naked_number Kind_naked_immediate)))
    (Or_unknown.Known
       (row_like_for_blocks_create_exactly tag (length fields) shape fields
          alloc_mode))
    No_extensions

(** val is_int_for_scrutinee : name -> flambda_type **)

let is_int_for_scrutinee scrutinee =
  Type_naked_immediate
    (Ok
       (No_alias
          { naked_immediates = Or_unknown.Known [Z0; Zpos Coq_xH];
            inverse_relations = (Relation.Is_int, scrutinee) :: []
          }))

(** val get_tag_for_block : name -> flambda_type **)

let get_tag_for_block block =
  Type_naked_immediate
    (Ok
       (No_alias
          { naked_immediates = Or_unknown.Unknown;
            inverse_relations = (Relation.Get_tag, block) :: []
          }))

(** val is_null_for_scrutinee : name -> flambda_type **)

let is_null_for_scrutinee scrutinee =
  Type_naked_immediate
    (Ok
       (No_alias
          { naked_immediates = Or_unknown.Known [Z0; Zpos Coq_xH];
            inverse_relations = (Relation.Is_null, scrutinee) :: []
          }))

(** val exactly_this_closure : function_slot -> function_type Or_unknown.t
    finite_map -> flambda_type finite_map -> flambda_type finite_map ->
    Alloc_mode.t -> flambda_type **)

let exactly_this_closure this_function_slot all_function_slots_in_set
    all_closure_types_in_set all_value_slots_in_set alloc_mode =
  create_closures alloc_mode
    (Row_like_for_closures
       (( this_function_slot,
          { case_maps_to =
              Closures_entry
                ( all_function_slots_in_set,
                  all_closure_types_in_set,
                  all_value_slots_in_set );
            case_index =
              { index_domain =
                  Row_like_index_domain.Known
                    { contents_closures = domain all_function_slots_in_set;
                      contents_value_slots = domain all_value_slots_in_set
                    };
                index_shape = ()
              };
            case_env_extension = empty_env_extension
          } )
       :: []))

(** val at_least_this_closure : function_slot -> function_type Or_unknown.t
    finite_map -> flambda_type finite_map -> flambda_type finite_map ->
    Alloc_mode.t -> flambda_type **)

let at_least_this_closure this_function_slot at_least_these_function_slots
    at_least_these_closure_types at_least_these_value_slots alloc_mode =
  create_closures alloc_mode
    (Row_like_for_closures
       (( this_function_slot,
          { case_maps_to =
              Closures_entry
                ( at_least_these_function_slots,
                  at_least_these_closure_types,
                  at_least_these_value_slots );
            case_index =
              { index_domain =
                  Row_like_index_domain.At_least
                    { contents_closures = domain at_least_these_function_slots;
                      contents_value_slots = domain at_least_these_value_slots
                    };
                index_shape = ()
              };
            case_env_extension = empty_env_extension
          } )
       :: []))

(** val free_variables_of_simple : simple -> variable list **)

let free_variables_of_simple = function Var x -> x :: [] | _ -> []

(** val free_variables_of_name : name -> variable list **)

let free_variables_of_name n = free_variables_of_simple (simple_of_name n)

(** val free_variables_of_option : variable option -> variable list **)

let free_variables_of_option = function Some x0 -> x0 :: [] | None -> []

(** val free_variables_of_descr : ('a1 -> variable list) -> 'a1 type_descr ->
    variable list **)

let free_variables_of_descr free_variables_of_head = function
  | Ok a -> (
    match a with
    | No_alias head -> free_variables_of_head head
    | Equals s -> free_variables_of_simple s)
  | _ -> []

(** val free_variables_of_naked_immediate : head_of_kind_naked_immediate ->
    variable list **)

let free_variables_of_naked_immediate head =
  flat_map
    (fun relation -> free_variables_of_name (snd relation))
    head.inverse_relations

(** val free_variables_of_block_case : (flambda_type -> variable list) ->
    (env_extension -> variable list) -> row_like_block_case -> variable list **)

let free_variables_of_block_case free_variables0
    free_variables_of_env_extension0 case =
  app
    (flat_map free_variables0 case.case_maps_to)
    (free_variables_of_env_extension0 case.case_env_extension)

(** val free_variables : flambda_type -> variable list **)

let rec free_variables = function
  | Type_value ty ->
    free_variables_of_descr free_variables_of_head_of_kind_value ty
  | Type_naked_immediate ty ->
    free_variables_of_descr free_variables_of_naked_immediate ty
  | Type_naked_number (_, ty) -> free_variables_of_descr (fun _ -> []) ty
  | Type_rec_info ty -> free_variables_of_descr (fun _ -> []) ty
  | Type_region ty -> free_variables_of_descr (fun _ -> []) ty

(** val free_variables_of_head_of_kind_value : head_of_kind_value -> variable
    list **)

and free_variables_of_head_of_kind_value = function
  | Head_of_kind_value (non_null, is_null0) ->
    app
      (match non_null with
      | Ok head0 -> free_variables_of_head_of_kind_value_non_null head0
      | _ -> [])
      (match is_null0 with
      | Not_null -> []
      | Maybe_null is_null1 -> free_variables_of_option is_null1)

(** val free_variables_of_head_of_kind_value_non_null :
    head_of_kind_value_non_null -> variable list **)

and free_variables_of_head_of_kind_value_non_null = function
  | Variant (is_int, immediates, get_tag, blocks, extensions, _) ->
    app
      (free_variables_of_option is_int)
      (app
         (match immediates with
         | Or_unknown.Known ty -> free_variables ty
         | Or_unknown.Unknown -> [])
         (app
            (free_variables_of_option get_tag)
            (app
               (match blocks with
               | Or_unknown.Known blocks0 ->
                 free_variables_of_row_like_for_blocks blocks0
               | Or_unknown.Unknown -> [])
               (match extensions with
               | No_extensions -> []
               | Ext (when_immediate, when_block) ->
                 app
                   (free_variables_of_env_extension when_immediate)
                   (free_variables_of_env_extension when_block)))))
  | Boxed_number (_, contents, _) -> free_variables contents
  | Closures (by_function_slot, _) ->
    free_variables_of_row_like_for_closures by_function_slot
  | _ -> []

(** val free_variables_of_row_like_for_blocks : row_like_for_blocks -> variable
    list **)

and free_variables_of_row_like_for_blocks = function
  | Row_like_for_blocks (known_tags, other_tags, _) ->
    app
      (flat_map
         (fun case ->
           match snd case with
           | Or_unknown.Known case0 ->
             free_variables_of_block_case free_variables
               free_variables_of_env_extension case0
           | Or_unknown.Unknown -> [])
         known_tags)
      (match other_tags with
      | Or_bottom.Ok case ->
        free_variables_of_block_case free_variables
          free_variables_of_env_extension case
      | Or_bottom.Bottom -> [])

(** val free_variables_of_row_like_for_closures : row_like_for_closures ->
    variable list **)

and free_variables_of_row_like_for_closures = function
  | Row_like_for_closures known_closures ->
    flat_map
      (fun case ->
        app
          (free_variables_of_closures_entry (snd case).case_maps_to)
          (free_variables_of_env_extension (snd case).case_env_extension))
      known_closures

(** val free_variables_of_closures_entry : closures_entry -> variable list **)

and free_variables_of_closures_entry = function
  | Closures_entry (_, closure_types, value_slot_types) ->
    app
      (flat_map (fun binding -> free_variables (snd binding)) closure_types)
      (flat_map (fun binding -> free_variables (snd binding)) value_slot_types)

(** val free_variables_of_env_extension : env_extension -> variable list **)

and free_variables_of_env_extension = function
  | Env_extension equations ->
    flat_map
      (fun binding ->
        app
          (free_variables_of_name (fst binding))
          (free_variables (snd binding)))
      equations
