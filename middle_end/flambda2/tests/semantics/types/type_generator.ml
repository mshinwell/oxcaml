(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* A generator of types of the Rocq model, and a shrinker of them.

   The generator goes through the grammar of FlambdaTypeGrammar.v: every
   constructor, of every kind; row-like structures of blocks and of closures
   with indexes that are known and that are known from below; variants with
   extensions; relations; aliases to variables, symbols and constants. It is
   seeded: the same seed gives the same types.

   What it makes is raw: it keeps none of what the creation functions of the
   compiler keep. A product may be wider than its index, a boxed number may hold
   a type of another kind, a map may bind a key twice, a set may be empty. From
   time to time, on purpose, it makes what the compiler cannot build at all (the
   allocation mode [Local], a number outside the range of its kind, a name that
   no name of the compiler is numbered by), so that the refusals of the
   converter are tested too. [well_formed], when set, turns those off and keeps
   kinds and sizes consistent, which is what gets a useful share of the types
   through the compiler's own functions.

   The names it uses are numbers of a pool that the caller numbered. *)

module M = Flambda2_rocq_semantics.FlambdaModel
module MK = Flambda2_rocq_semantics.FlambdaKindModel
module MT = Flambda2_rocq_semantics.FlambdaTypeGrammar
module N = Flambda2_rocq_types_converter.Model_numbers
module Random = Minicheck.Splittable_random

(* The numbers of the names that may be used, by sort; the variables by kind. *)
type pool =
  { value_variables : M.variable list;
    naked_immediate_variables : M.variable list;
    naked_float_variables : M.variable list;
    region_variables : M.variable list;
    rec_info_variables : M.variable list;
    symbols : M.symbol list;
    code_ids : M.code_id list;
    function_slots : M.function_slot list;
    value_slots : M.value_slot list;
    (* A number that is no name of the compiler. *)
    unknown_name : N.positive
  }

type config =
  { well_formed : bool;
    depth : int
  }

(* ---- Randomness -------------------------------------------------------- *)

let below r n = if n <= 0 then 0 else Int.abs (Random.int r) mod n

let chance r ~percent = below r 100 < percent

let pick r items = List.nth items (below r (List.length items))

let list r ~max gen = List.init (below r (max + 1)) (fun _ -> gen ())

(* ---- Pieces ------------------------------------------------------------ *)

let all_naked_number_kinds : MK.naked_number_kind list =
  [ Kind_naked_immediate;
    Kind_naked_float32;
    Kind_naked_float;
    Kind_naked_int8;
    Kind_naked_int16;
    Kind_naked_int32;
    Kind_naked_int64;
    Kind_naked_nativeint;
    Kind_naked_vec128;
    Kind_naked_vec256;
    Kind_naked_vec512;
    Kind_naked_mask ]

let all_boxable_numbers : MK.boxable_number list =
  [ Boxable_naked_float32;
    Boxable_naked_float;
    Boxable_naked_int32;
    Boxable_naked_int64;
    Boxable_naked_nativeint;
    Boxable_naked_vec128;
    Boxable_naked_vec256;
    Boxable_naked_vec512;
    Boxable_naked_mask ]

(* The kinds of the numbers that are boxed, in the order of the list above. *)
let boxable_kinds : MK.naked_number_kind list =
  List.filter
    (fun k -> Option.is_some (MK.boxable_number_of_kind (MK.Naked_number k)))
    all_naked_number_kinds

let all_kinds : MK.flambda_kind list =
  (MK.Value :: List.map (fun k -> MK.Naked_number k) all_naked_number_kinds)
  @ [MK.Region; MK.Rec_info]

let kind r : MK.flambda_kind =
  if chance r ~percent:55
  then Value
  else if chance r ~percent:40
  then Naked_number Kind_naked_immediate
  else pick r all_kinds

let is_naked_immediate (k : MK.naked_number_kind) =
  match k with
  | Kind_naked_immediate -> true
  | Kind_naked_float32 | Kind_naked_float | Kind_naked_int8 | Kind_naked_int16
  | Kind_naked_int32 | Kind_naked_int64 | Kind_naked_nativeint
  | Kind_naked_vec128 | Kind_naked_vec256 | Kind_naked_vec512 | Kind_naked_mask
    ->
    false

let small_number r = N.z_of_int (below r 7 - 2)

(* A number of a kind: small, and in range unless the type is to be one that the
   compiler cannot build. *)
let number config r (k : MK.naked_number_kind) : N.z =
  if (not config.well_formed) && chance r ~percent:3
  then
    (* Out of the range of every kind but the 512-bit vectors. *)
    N.z_of_words [0L; 0L; 0L; 0L; 1L]
  else
    match k with
    | Kind_naked_immediate | Kind_naked_int8 | Kind_naked_int16
    | Kind_naked_int32 | Kind_naked_int64 | Kind_naked_nativeint ->
      small_number r
    | Kind_naked_float32 | Kind_naked_float | Kind_naked_vec128
    | Kind_naked_vec256 | Kind_naked_vec512 | Kind_naked_mask ->
      N.z_of_int (below r 5)

let alloc_mode config r : MT.Alloc_mode.t =
  if (not config.well_formed) && chance r ~percent:3
  then Local
  else if chance r ~percent:50
  then Heap
  else Heap_or_local

let name_of config r pool names =
  if (not config.well_formed) && chance r ~percent:2
  then pool.unknown_name
  else pick r names

let variables_of_kind pool (k : MK.flambda_kind) : M.variable list =
  match k with
  | Value -> pool.value_variables
  | Naked_number Kind_naked_immediate -> pool.naked_immediate_variables
  | Naked_number Kind_naked_float -> pool.naked_float_variables
  | Naked_number
      ( Kind_naked_float32 | Kind_naked_int8 | Kind_naked_int16
      | Kind_naked_int32 | Kind_naked_int64 | Kind_naked_nativeint
      | Kind_naked_vec128 | Kind_naked_vec256 | Kind_naked_vec512
      | Kind_naked_mask ) ->
    []
  | Region -> pool.region_variables
  | Rec_info -> pool.rec_info_variables

let const_of_kind config r (k : MK.flambda_kind) : M.const option =
  match k with
  | Value ->
    Some
      (if chance r ~percent:15
       then Null
       else if chance r ~percent:10
       then Poison Value
       else Tagged_immediate (small_number r))
  | Naked_number k ->
    let n = number config r k in
    Some
      (match k with
      | Kind_naked_immediate -> Naked_immediate n
      | Kind_naked_float32 -> Naked_float32 n
      | Kind_naked_float -> Naked_float n
      | Kind_naked_int8 -> Naked_int8 n
      | Kind_naked_int16 -> Naked_int16 n
      | Kind_naked_int32 -> Naked_int32 n
      | Kind_naked_int64 -> Naked_int64 n
      | Kind_naked_nativeint -> Naked_nativeint n
      | Kind_naked_vec128 -> Naked_vec128 n
      | Kind_naked_vec256 -> Naked_vec256 n
      | Kind_naked_vec512 -> Naked_vec512 n
      | Kind_naked_mask -> Naked_mask n)
  | Region | Rec_info -> None

(* A [Simple] of a kind, if the pool has one. *)
let simple config r pool (k : MK.flambda_kind) : M.simple option =
  let variable () =
    match variables_of_kind pool k with
    | [] -> None
    | _ :: _ as variables -> Some (M.Var (name_of config r pool variables))
  in
  let const () =
    Option.map (fun const -> M.Const const) (const_of_kind config r k)
  in
  let symbol () =
    match k with
    | Value -> Some (M.Symbol (name_of config r pool pool.symbols))
    | Naked_number _ | Region | Rec_info -> None
  in
  let first_of choices = List.find_map (fun choice -> choice ()) choices in
  match below r 3 with
  | 0 -> first_of [symbol; variable; const]
  | 1 -> first_of [const; variable]
  | _ -> first_of [variable; const]

let name config r pool : MT.name =
  if chance r ~percent:25
  then Name_symbol (name_of config r pool pool.symbols)
  else Name_var (name_of config r pool pool.value_variables)

let option r gen = if chance r ~percent:50 then Some (gen ()) else None

let naked_immediate_variable config r pool =
  name_of config r pool pool.naked_immediate_variables

let relation r : MT.Relation.t =
  pick r [MT.Relation.Is_null; MT.Relation.Is_int; MT.Relation.Get_tag]

let block_shape r : MT.block_shape =
  match below r 10 with
  | 0 -> Float_record
  | 1 | 2 ->
    Scannable
      (Mixed_record
         ( N.nat_of_int (below r 3),
           list r ~max:2 (fun () -> pick r all_naked_number_kinds) ))
  | _ -> Scannable Value_only

let unknown_or_bottom r (k : MK.flambda_kind) : MT.flambda_type =
  if chance r ~percent:75 then MT.unknown k else MT.bottom k

(* ---- Types ------------------------------------------------------------- *)

let rec type_of_kind config r pool (k : MK.flambda_kind) : MT.flambda_type =
  let descr head : _ MT.type_descr =
    match below r 10 with
    | 0 -> Unknown
    | 1 -> Bottom
    | 2 | 3 -> (
      match simple config r pool k with
      | Some simple -> Ok (Equals simple)
      | None -> Unknown)
    | _ -> Ok (No_alias (head ()))
  in
  if config.depth <= 0
  then unknown_or_bottom r k
  else
    match k with
    | Value -> Type_value (descr (fun () -> head_of_kind_value config r pool))
    | Naked_number k
      when is_naked_immediate k && (config.well_formed || chance r ~percent:97)
      ->
      ignore (k : MK.naked_number_kind);
      Type_naked_immediate
        (descr (fun () : MT.head_of_kind_naked_immediate ->
             { naked_immediates =
                 (if chance r ~percent:30
                  then Unknown
                  else
                    Known
                      (small_number r
                      :: list r ~max:2 (fun () -> small_number r)));
               inverse_relations =
                 list r ~max:2 (fun () -> relation r, name config r pool)
             }))
    | Naked_number k ->
      Type_naked_number
        ( k,
          descr (fun () ->
              let numbers = list r ~max:2 (fun () -> number config r k) in
              if config.well_formed || chance r ~percent:95
              then number config r k :: numbers
              else numbers) )
    | Rec_info -> Type_rec_info (descr (fun () -> ()))
    | Region -> Type_region (descr (fun () -> ()))

and deeper config = { config with depth = config.depth - 1 }

and head_of_kind_value config r pool : MT.head_of_kind_value =
  Head_of_kind_value
    ( (match below r 8 with
      | 0 -> Unknown
      | 1 -> Bottom
      | _ -> Ok (head_of_kind_value_non_null config r pool)),
      match below r 4 with
      | 0 -> Maybe_null None
      | 1 -> Maybe_null (Some (naked_immediate_variable config r pool))
      | _ -> Not_null )

and head_of_kind_value_non_null config r pool : MT.head_of_kind_value_non_null =
  let sub = deeper config in
  match below r 10 with
  | 0 -> Mutable_block (alloc_mode config r)
  | 1 ->
    (* The type in the box is of the kind of the number boxed, except, one time
       in ten when types that are not well formed are wanted, of another kind of
       number. *)
    let number = pick r all_boxable_numbers in
    let contents_kind =
      if config.well_formed || chance r ~percent:90
      then MK.unboxed_kind number
      else MK.Naked_number (pick r all_naked_number_kinds)
    in
    Boxed_number
      (number, type_of_kind sub r pool contents_kind, alloc_mode config r)
  | 2 | 3 -> Closures (row_like_for_closures sub r pool, alloc_mode config r)
  | 4 ->
    String
      (list r ~max:2 (fun () ->
           list r ~max:3 (fun () ->
               if config.well_formed || chance r ~percent:97
               then N.z_of_int (97 + below r 3)
               else N.z_of_int 256)))
  | _ ->
    Variant
      ( option r (fun () -> naked_immediate_variable config r pool),
        (if chance r ~percent:30
         then Unknown
         else
           Known
             (type_of_kind sub r pool
                (if config.well_formed || chance r ~percent:95
                 then MK.Naked_number Kind_naked_immediate
                 else kind r))),
        option r (fun () -> naked_immediate_variable config r pool),
        (if chance r ~percent:25
         then Unknown
         else Known (row_like_for_blocks sub r pool)),
        (if chance r ~percent:80
         then No_extensions
         else Ext (env_extension sub r pool, env_extension sub r pool)),
        chance r ~percent:10 )

and block_case config r pool : MT.row_like_block_case =
  let shape = block_shape r in
  let size = below r 4 in
  let shape, size =
    (* A mixed block has the size that its shape gives it. *)
    match shape with
    | Scannable (Mixed_record (value_prefix_size, flat_suffix))
      when config.well_formed ->
      shape, N.int_of_nat value_prefix_size + List.length flat_suffix
    | Scannable (Value_only | Mixed_record _) | Float_record -> shape, size
  in
  let width =
    if config.well_formed || chance r ~percent:80
    then below r (size + 1)
    else below r 5
  in
  let kinds = MT.field_kinds shape (N.nat_of_int size) in
  let field i =
    type_of_kind config r pool
      (match List.nth_opt kinds i with
      | Some k when config.well_formed || chance r ~percent:90 -> k
      | Some _ | None -> kind r)
  in
  { case_maps_to = List.init width field;
    case_index =
      { index_domain =
          (if chance r ~percent:60
           then Known (N.nat_of_int size)
           else At_least (N.nat_of_int size));
        index_shape = shape
      };
    case_env_extension = env_extension config r pool
  }

and row_like_for_blocks config r pool : MT.row_like_for_blocks =
  let scannable_tag () = N.z_of_int (pick r [0; 1; 2; 3; 250]) in
  let any_tag () =
    if chance r ~percent:97
    then N.z_of_int (pick r [0; 1; 2; 3; 250; 254])
    else N.z_of_int 256
  in
  (* The tag of a case is one that its shape permits. *)
  let tag_of_shape (shape : MT.block_shape) =
    if not config.well_formed
    then any_tag ()
    else
      match shape with
      | Scannable (Value_only | Mixed_record _) -> scannable_tag ()
      | Float_record -> MT.double_array_tag
  in
  Row_like_for_blocks
    ( list r ~max:3 (fun () ->
          if chance r ~percent:20
          then
            ( (if config.well_formed then scannable_tag () else any_tag ()),
              MT.Or_unknown.Unknown )
          else
            let case = block_case config r pool in
            tag_of_shape case.case_index.index_shape, MT.Or_unknown.Known case),
      (if chance r ~percent:80 then Bottom else Ok (block_case config r pool)),
      alloc_mode config r )

and contents config r pool : MT.set_of_closures_contents =
  { contents_closures =
      list r ~max:2 (fun () -> name_of config r pool pool.function_slots);
    contents_value_slots =
      list r ~max:2 (fun () -> name_of config r pool pool.value_slots)
  }

and row_like_for_closures config r pool : MT.row_like_for_closures =
  Row_like_for_closures
    (list r ~max:2 (fun () ->
         ( name_of config r pool pool.function_slots,
           ({ case_maps_to = closures_entry config r pool;
              case_index =
                { index_domain =
                    (if chance r ~percent:50
                     then Known (contents config r pool)
                     else At_least (contents config r pool));
                  index_shape = ()
                };
              case_env_extension = env_extension config r pool
            }
             : (_, _, _, _) MT.row_like_case) )))

and closures_entry config r pool : MT.closures_entry =
  Closures_entry
    ( list r ~max:2 (fun () ->
          ( name_of config r pool pool.function_slots,
            if chance r ~percent:20
            then MT.Or_unknown.Unknown
            else
              MT.Or_unknown.Known
                { MT.function_type_code_id = name_of config r pool pool.code_ids
                } )),
      list r ~max:2 (fun () ->
          ( name_of config r pool pool.function_slots,
            type_of_kind config r pool
              (if config.well_formed || chance r ~percent:90
               then MK.Value
               else kind r) )),
      list r ~max:2 (fun () ->
          ( name_of config r pool pool.value_slots,
            (* The value slots of the pool are of kind value. *)
            type_of_kind config r pool
              (if config.well_formed then MK.Value else kind r) )) )

and env_extension config r pool : MT.env_extension =
  Env_extension
    (if chance r ~percent:75
     then []
     else
       list r ~max:2 (fun () ->
           name config r pool, type_of_kind (deeper config) r pool MK.Value))

let flambda_type config r pool : MT.flambda_type =
  type_of_kind config r pool (kind r)

(* ---- Shrinking ---------------------------------------------------------- *)

(* The types to try in place of a type that makes a test fail: each has one part
   made smaller or removed. They are tried in order. *)

let shrink_list shrink_item items =
  let rec without i = function
    | [] -> []
    | item :: items -> if i = 0 then items else item :: without (i - 1) items
  in
  let rec with_item i shrunk = function
    | [] -> []
    | item :: items ->
      if i = 0 then shrunk :: items else item :: with_item (i - 1) shrunk items
  in
  List.mapi (fun i _ -> without i items) items
  @ List.concat
      (List.mapi
         (fun i item ->
           List.map (fun shrunk -> with_item i shrunk items) (shrink_item item))
         items)

let shrink_map shrink_value bindings =
  shrink_list
    (fun (key, value) ->
      List.map (fun value -> key, value) (shrink_value value))
    bindings

let no_shrink _ = []

let shrink_or_unknown shrink (x : _ MT.Or_unknown.t) : _ MT.Or_unknown.t list =
  match x with
  | Unknown -> []
  | Known x -> Unknown :: List.map (fun x -> MT.Or_unknown.Known x) (shrink x)

let shrink_option x = match x with None -> [] | Some _ -> [None]

let rec shrink (t : MT.flambda_type) : MT.flambda_type list =
  let descr rebuild shrink_head (ty : _ MT.type_descr) =
    match ty with
    | Unknown -> []
    | Bottom | Ok (Equals _) -> [MT.unknown (MT.kind t)]
    | Ok (No_alias head) ->
      MT.unknown (MT.kind t)
      :: List.map
           (fun head -> rebuild (MT.Ok (MT.No_alias head)))
           (shrink_head head)
  in
  match t with
  | Type_value ty ->
    descr (fun ty -> MT.Type_value ty) shrink_head_of_kind_value ty
  | Type_naked_immediate ty ->
    descr
      (fun ty -> MT.Type_naked_immediate ty)
      (fun (head : MT.head_of_kind_naked_immediate) ->
        List.map
          (fun naked_immediates : MT.head_of_kind_naked_immediate ->
            { head with naked_immediates })
          (shrink_or_unknown (shrink_list no_shrink) head.naked_immediates)
        @ List.map
            (fun inverse_relations : MT.head_of_kind_naked_immediate ->
              { head with inverse_relations })
            (shrink_list no_shrink head.inverse_relations))
      ty
  | Type_naked_number (k, ty) ->
    descr (fun ty -> MT.Type_naked_number (k, ty)) (shrink_list no_shrink) ty
  | Type_rec_info ty -> descr (fun ty -> MT.Type_rec_info ty) no_shrink ty
  | Type_region ty -> descr (fun ty -> MT.Type_region ty) no_shrink ty

and shrink_head_of_kind_value
    (Head_of_kind_value (non_null, is_null) : MT.head_of_kind_value) :
    MT.head_of_kind_value list =
  (match is_null with
    | Not_null -> []
    | Maybe_null None -> [MT.Head_of_kind_value (non_null, Not_null)]
    | Maybe_null (Some _) ->
      let is_null : MT.is_null = Maybe_null None in
      [MT.Head_of_kind_value (non_null, is_null)])
  @
  match non_null with
  | Unknown -> []
  | Bottom -> [MT.Head_of_kind_value (Unknown, is_null)]
  | Ok head ->
    MT.Head_of_kind_value (Unknown, is_null)
    :: List.map
         (fun head -> MT.Head_of_kind_value (MT.Ok head, is_null))
         (shrink_head_of_kind_value_non_null head)

and shrink_head_of_kind_value_non_null (head : MT.head_of_kind_value_non_null) :
    MT.head_of_kind_value_non_null list =
  match head with
  | Variant (is_int, immediates, get_tag, blocks, extensions, is_unique) ->
    let variant is_int immediates get_tag blocks extensions is_unique =
      MT.Variant (is_int, immediates, get_tag, blocks, extensions, is_unique)
    in
    List.map
      (fun is_int ->
        variant is_int immediates get_tag blocks extensions is_unique)
      (shrink_option is_int)
    @ List.map
        (fun get_tag ->
          variant is_int immediates get_tag blocks extensions is_unique)
        (shrink_option get_tag)
    @ (match extensions with
      | No_extensions -> []
      | Ext (when_immediate, when_block) ->
        variant is_int immediates get_tag blocks MT.No_extensions is_unique
        :: (List.map
              (fun ext ->
                variant is_int immediates get_tag blocks
                  (MT.Ext (ext, when_block))
                  is_unique)
              (shrink_env_extension when_immediate)
           @ List.map
               (fun ext ->
                 variant is_int immediates get_tag blocks
                   (MT.Ext (when_immediate, ext))
                   is_unique)
               (shrink_env_extension when_block)))
    @ List.map
        (fun immediates ->
          variant is_int immediates get_tag blocks extensions is_unique)
        (shrink_or_unknown shrink immediates)
    @ List.map
        (fun blocks ->
          variant is_int immediates get_tag blocks extensions is_unique)
        (shrink_or_unknown shrink_row_like_for_blocks blocks)
    @
    if is_unique
    then [variant is_int immediates get_tag blocks extensions false]
    else []
  | Mutable_block _ -> []
  | Boxed_number (k, contents, alloc_mode) ->
    List.map
      (fun contents -> MT.Boxed_number (k, contents, alloc_mode))
      (shrink contents)
  | Closures (Row_like_for_closures known_closures, alloc_mode) ->
    List.map
      (fun known_closures ->
        MT.Closures (MT.Row_like_for_closures known_closures, alloc_mode))
      (shrink_map
         (fun (case : (_, _, _, _) MT.row_like_case) ->
           List.map
             (fun case_maps_to : (_, _, _, _) MT.row_like_case ->
               { case with case_maps_to })
             (shrink_closures_entry case.case_maps_to)
           @ List.map
               (fun case_env_extension : (_, _, _, _) MT.row_like_case ->
                 { case with case_env_extension })
               (shrink_env_extension case.case_env_extension))
         known_closures)
  | String strs ->
    List.map
      (fun strs -> MT.String strs)
      (shrink_list (shrink_list no_shrink) strs)

and shrink_block_case (case : MT.row_like_block_case) :
    MT.row_like_block_case list =
  List.map
    (fun case_maps_to : MT.row_like_block_case -> { case with case_maps_to })
    (shrink_list shrink case.case_maps_to)
  @ List.map
      (fun case_env_extension : MT.row_like_block_case ->
        { case with case_env_extension })
      (shrink_env_extension case.case_env_extension)

and shrink_row_like_for_blocks
    (Row_like_for_blocks (known_tags, other_tags, alloc_mode) :
      MT.row_like_for_blocks) : MT.row_like_for_blocks list =
  List.map
    (fun known_tags ->
      MT.Row_like_for_blocks (known_tags, other_tags, alloc_mode))
    (shrink_map (shrink_or_unknown shrink_block_case) known_tags)
  @
  match other_tags with
  | Bottom -> []
  | Ok case ->
    MT.Row_like_for_blocks (known_tags, Bottom, alloc_mode)
    :: List.map
         (fun case ->
           let other_tags = MT.Or_bottom.Ok case in
           MT.Row_like_for_blocks (known_tags, other_tags, alloc_mode))
         (shrink_block_case case)

and shrink_closures_entry
    (Closures_entry (function_types, closure_types, value_slot_types) :
      MT.closures_entry) : MT.closures_entry list =
  List.map
    (fun function_types ->
      MT.Closures_entry (function_types, closure_types, value_slot_types))
    (shrink_map (shrink_or_unknown no_shrink) function_types)
  @ List.map
      (fun closure_types ->
        MT.Closures_entry (function_types, closure_types, value_slot_types))
      (shrink_map shrink closure_types)
  @ List.map
      (fun value_slot_types ->
        MT.Closures_entry (function_types, closure_types, value_slot_types))
      (shrink_map shrink value_slot_types)

and shrink_env_extension (Env_extension equations : MT.env_extension) :
    MT.env_extension list =
  List.map
    (fun equations -> MT.Env_extension equations)
    (shrink_map shrink equations)
