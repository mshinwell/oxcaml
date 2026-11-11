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

(* The types of the Rocq model, for the tests: when two of them are the same,
   and how they are printed.

   A type of the model holds maps, which are association lists of which the
   first binding of a key counts, and sets, which are lists. Two types are the
   same when they differ only in how their maps and sets are written: that is
   the equality of maps of the model ([map_equal], FlambdaMapSpec.v) and the
   equality of lists as sets, taken through the whole type. [normalise] writes
   every map and every set of a type in one way (a map without its shadowed
   bindings, in the order of its keys; a set in order, without repeats), so that
   two types are the same when their normal forms are equal.

   This is part of what the tests are trusted for: if [same] said yes of types
   that differ in more than that, a disagreement would go unseen. It is not part
   of the conversion. *)

module M = Flambda2_rocq_semantics.FlambdaModel
module MK = Flambda2_rocq_semantics.FlambdaKindModel
module MT = Flambda2_rocq_semantics.FlambdaTypeGrammar
module N = Model_numbers

(* ---- Orders on keys ---------------------------------------------------- *)

let compare_name (n : MT.name) (n' : MT.name) =
  match n, n' with
  | Name_var x, Name_var x' -> N.compare_positive x x'
  | Name_symbol s, Name_symbol s' -> N.compare_positive s s'
  | Name_var _, Name_symbol _ -> -1
  | Name_symbol _, Name_var _ -> 1

let relation_rank (relation : MT.Relation.t) =
  match relation with Is_null -> 0 | Is_int -> 1 | Get_tag -> 2

let compare_relation_and_name (relation, name) (relation', name') =
  let c = Int.compare (relation_rank relation) (relation_rank relation') in
  if c <> 0 then c else compare_name name name'

(* ---- Maps and sets in one way ----------------------------------------- *)

(* A set, as a list in order without repeats. *)
let set compare elements = List.sort_uniq compare elements

(* A map, without the bindings that an earlier one shadows, in the order of its
   keys. *)
let map compare_key normalise_value bindings =
  let first_bindings =
    List.fold_left
      (fun kept (key, value) ->
        if List.exists (fun (key', _) -> compare_key key key' = 0) kept
        then kept
        else (key, normalise_value value) :: kept)
      [] bindings
  in
  List.sort (fun (key, _) (key', _) -> compare_key key key') first_bindings

let compare_bytes = List.compare N.compare_z

(* ---- The normal form of a type ---------------------------------------- *)

let or_unknown f (x : _ MT.Or_unknown.t) : _ MT.Or_unknown.t =
  match x with Known x -> Known (f x) | Unknown -> Unknown

let or_bottom f (x : _ MT.Or_bottom.t) : _ MT.Or_bottom.t =
  match x with Ok x -> Ok (f x) | Bottom -> Bottom

let descr head (ty : _ MT.type_descr) : _ MT.type_descr =
  match ty with
  | Unknown -> Unknown
  | Bottom -> Bottom
  | Ok (No_alias h) -> Ok (No_alias (head h))
  | Ok (Equals simple) -> Ok (Equals simple)

let rec normalise (t : MT.flambda_type) : MT.flambda_type =
  match t with
  | Type_value ty -> Type_value (descr head_of_kind_value ty)
  | Type_naked_immediate ty ->
    Type_naked_immediate
      (descr
         (fun (head : MT.head_of_kind_naked_immediate) :
              MT.head_of_kind_naked_immediate ->
           { naked_immediates =
               or_unknown (set N.compare_z) head.naked_immediates;
             inverse_relations =
               set compare_relation_and_name head.inverse_relations
           })
         ty)
  | Type_naked_number (kind, ty) ->
    Type_naked_number (kind, descr (set N.compare_z) ty)
  | Type_rec_info ty -> Type_rec_info ty
  | Type_region ty -> Type_region ty

and head_of_kind_value
    (Head_of_kind_value (non_null, is_null) : MT.head_of_kind_value) :
    MT.head_of_kind_value =
  Head_of_kind_value
    ( (match non_null with
      | Unknown -> Unknown
      | Bottom -> Bottom
      | Ok head -> Ok (head_of_kind_value_non_null head)),
      is_null )

and head_of_kind_value_non_null (head : MT.head_of_kind_value_non_null) :
    MT.head_of_kind_value_non_null =
  match head with
  | Variant (is_int, immediates, get_tag, blocks, extensions, is_unique) ->
    Variant
      ( is_int,
        or_unknown normalise immediates,
        get_tag,
        or_unknown row_like_for_blocks blocks,
        (match extensions with
        | No_extensions -> No_extensions
        | Ext (when_immediate, when_block) ->
          Ext (env_extension when_immediate, env_extension when_block)),
        is_unique )
  | Mutable_block alloc_mode -> Mutable_block alloc_mode
  | Boxed_number (number, contents, alloc_mode) ->
    Boxed_number (number, normalise contents, alloc_mode)
  | Closures (Row_like_for_closures known_closures, alloc_mode) ->
    Closures
      ( Row_like_for_closures
          (map N.compare_positive
             (fun (case : (_, _, _, _) MT.row_like_case) :
                  (_, _, _, _) MT.row_like_case ->
               { case_maps_to = closures_entry case.case_maps_to;
                 case_index =
                   { index_domain =
                       (match case.case_index.index_domain with
                       | Known contents -> Known (contents_of_set contents)
                       | At_least contents ->
                         At_least (contents_of_set contents));
                     index_shape = case.case_index.index_shape
                   };
                 case_env_extension = env_extension case.case_env_extension
               })
             known_closures),
        alloc_mode )
  | String strs -> String (set compare_bytes strs)

and contents_of_set (contents : MT.set_of_closures_contents) :
    MT.set_of_closures_contents =
  { contents_closures = set N.compare_positive contents.contents_closures;
    contents_value_slots = set N.compare_positive contents.contents_value_slots
  }

and block_case (case : MT.row_like_block_case) : MT.row_like_block_case =
  { case_maps_to = List.map normalise case.case_maps_to;
    case_index = case.case_index;
    case_env_extension = env_extension case.case_env_extension
  }

and row_like_for_blocks
    (Row_like_for_blocks (known_tags, other_tags, alloc_mode) :
      MT.row_like_for_blocks) : MT.row_like_for_blocks =
  Row_like_for_blocks
    ( map N.compare_z (or_unknown block_case) known_tags,
      or_bottom block_case other_tags,
      alloc_mode )

and closures_entry
    (Closures_entry (function_types, closure_types, value_slot_types) :
      MT.closures_entry) : MT.closures_entry =
  Closures_entry
    ( map N.compare_positive Fun.id function_types,
      map N.compare_positive normalise closure_types,
      map N.compare_positive normalise value_slot_types )

and env_extension (Env_extension equations : MT.env_extension) :
    MT.env_extension =
  Env_extension (map compare_name normalise equations)

(* The same type, up to how its maps and sets are written. *)
let same (t : MT.flambda_type) (t' : MT.flambda_type) : bool =
  Stdlib.( = ) (normalise t) (normalise t')

(* The same list of variables as a set. *)
let same_variables (xs : M.variable list) (xs' : M.variable list) : bool =
  Stdlib.( = ) (set N.compare_positive xs) (set N.compare_positive xs')

(* ---- Extensions within extensions ------------------------------------- *)

(* How deep the environment extensions of a type that have an equation are
   inside one another: 0 if it has none, 1 if none of the types of its
   extensions has one, and so on. *)
let rec extension_depth (t : MT.flambda_type) : int =
  let deepest depths = List.fold_left Int.max 0 depths in
  let of_extension (Env_extension equations : MT.env_extension) =
    match equations with
    | [] -> 0
    | _ :: _ ->
      1 + deepest (List.map (fun (_, t) -> extension_depth t) equations)
  in
  let of_block_case (case : MT.row_like_block_case) =
    deepest
      (of_extension case.case_env_extension
      :: List.map extension_depth case.case_maps_to)
  in
  let of_head (head : MT.head_of_kind_value_non_null) =
    match head with
    | Variant (_, immediates, _, blocks, extensions, _) ->
      deepest
        [ (match immediates with Known t -> extension_depth t | Unknown -> 0);
          (match blocks with
          | Unknown -> 0
          | Known (Row_like_for_blocks (known_tags, other_tags, _)) ->
            deepest
              ((match other_tags with
               | Ok case -> of_block_case case
               | Bottom -> 0)
              :: List.map
                   (fun (_, (case : _ MT.Or_unknown.t)) ->
                     match case with
                     | Known case -> of_block_case case
                     | Unknown -> 0)
                   known_tags));
          (match extensions with
          | No_extensions -> 0
          | Ext (when_immediate, when_block) ->
            Int.max (of_extension when_immediate) (of_extension when_block)) ]
    | Mutable_block _ | String _ -> 0
    | Boxed_number (_, contents, _) -> extension_depth contents
    | Closures (Row_like_for_closures cases, _) ->
      deepest
        (List.map
           (fun (_, (case : (_, _, _, _) MT.row_like_case)) ->
             let (Closures_entry (_, closure_types, value_slot_types)
                   : MT.closures_entry) =
               case.case_maps_to
             in
             deepest
               (of_extension case.case_env_extension
               :: List.map
                    (fun (_, t) -> extension_depth t)
                    (closure_types @ value_slot_types)))
           cases)
  in
  match t with
  | Type_value (Ok (No_alias (Head_of_kind_value (non_null, _)))) -> (
    match non_null with Ok head -> of_head head | Unknown | Bottom -> 0)
  | Type_value (Unknown | Bottom | Ok (Equals _))
  | Type_naked_immediate _ | Type_naked_number _ | Type_rec_info _
  | Type_region _ ->
    0

(* ---- Printing --------------------------------------------------------- *)

let print_list print ppf items =
  Format.fprintf ppf "@[<hov 1>[%a]@]"
    (Format.pp_print_list
       ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
       print)
    items

let print_option print ppf x =
  match x with
  | None -> Format.pp_print_string ppf "None"
  | Some x -> Format.fprintf ppf "(Some %a)" print x

let print_variable ppf x = Format.fprintf ppf "v%a" N.print_positive x

let print_symbol ppf s = Format.fprintf ppf "$%a" N.print_positive s

let print_naked_number_kind ppf (kind : MK.naked_number_kind) =
  Format.pp_print_string ppf
    (match kind with
    | Kind_naked_immediate -> "naked_immediate"
    | Kind_naked_float32 -> "naked_float32"
    | Kind_naked_float -> "naked_float"
    | Kind_naked_int8 -> "naked_int8"
    | Kind_naked_int16 -> "naked_int16"
    | Kind_naked_int32 -> "naked_int32"
    | Kind_naked_int64 -> "naked_int64"
    | Kind_naked_nativeint -> "naked_nativeint"
    | Kind_naked_vec128 -> "naked_vec128"
    | Kind_naked_vec256 -> "naked_vec256"
    | Kind_naked_vec512 -> "naked_vec512"
    | Kind_naked_mask -> "naked_mask")

let print_kind ppf (kind : MK.flambda_kind) =
  match kind with
  | Value -> Format.pp_print_string ppf "value"
  | Naked_number kind -> print_naked_number_kind ppf kind
  | Region -> Format.pp_print_string ppf "region"
  | Rec_info -> Format.pp_print_string ppf "rec_info"

let print_const ppf (const : M.const) =
  let number name n = Format.fprintf ppf "%s %a" name N.print_z n in
  match const with
  | Naked_immediate i -> number "#" i
  | Tagged_immediate i -> N.print_z ppf i
  | Naked_float32 f -> number "float32" f
  | Naked_float f -> number "float" f
  | Naked_int8 i -> number "int8" i
  | Naked_int16 i -> number "int16" i
  | Naked_int32 i -> number "int32" i
  | Naked_int64 i -> number "int64" i
  | Naked_nativeint i -> number "nativeint" i
  | Naked_vec128 v -> number "vec128" v
  | Naked_vec256 v -> number "vec256" v
  | Naked_vec512 v -> number "vec512" v
  | Naked_mask m -> number "mask" m
  | Null -> Format.pp_print_string ppf "null"
  | Poison kind -> Format.fprintf ppf "poison:%a" print_kind kind

let print_simple ppf (simple : M.simple) =
  match simple with
  | Var x -> print_variable ppf x
  | Symbol s -> print_symbol ppf s
  | Const const -> print_const ppf const

let print_name ppf (name : MT.name) =
  match name with
  | Name_var x -> print_variable ppf x
  | Name_symbol s -> print_symbol ppf s

let print_alloc_mode ppf (mode : MT.Alloc_mode.t) =
  Format.pp_print_string ppf
    (match mode with
    | Heap -> "Heap"
    | Local -> "Local"
    | Heap_or_local -> "Heap_or_local")

let print_relation ppf (relation : MT.Relation.t) =
  Format.pp_print_string ppf
    (match relation with
    | Is_null -> "Is_null"
    | Is_int -> "Is_int"
    | Get_tag -> "Get_tag")

let print_or_unknown print ppf (x : _ MT.Or_unknown.t) =
  match x with
  | Known x -> Format.fprintf ppf "@[<hov 1>(Known@ %a)@]" print x
  | Unknown -> Format.pp_print_string ppf "Unknown"

let print_or_bottom print ppf (x : _ MT.Or_bottom.t) =
  match x with
  | Ok x -> Format.fprintf ppf "@[<hov 1>(Ok@ %a)@]" print x
  | Bottom -> Format.pp_print_string ppf "Bottom"

let print_descr print_head ppf (ty : _ MT.type_descr) =
  match ty with
  | Unknown -> Format.pp_print_string ppf "Unknown"
  | Bottom -> Format.pp_print_string ppf "Bottom"
  | Ok (No_alias head) -> print_head ppf head
  | Ok (Equals simple) -> Format.fprintf ppf "(= %a)" print_simple simple

let print_index_domain print ppf (domain : _ MT.Row_like_index_domain.t) =
  match domain with
  | Known index -> Format.fprintf ppf "@[<hov 1>(Known@ %a)@]" print index
  | At_least index -> Format.fprintf ppf "@[<hov 1>(At_least@ %a)@]" print index

let print_block_shape ppf (shape : MT.block_shape) =
  match shape with
  | Scannable Value_only -> Format.pp_print_string ppf "Value_only"
  | Scannable (Mixed_record (value_prefix_size, flat_suffix)) ->
    Format.fprintf ppf "@[<hov 1>(Mixed_record@ %a@ %a)@]" N.print_nat
      value_prefix_size
      (print_list print_naked_number_kind)
      flat_suffix
  | Float_record -> Format.pp_print_string ppf "Float_record"

let print_map print_key print_value ppf bindings =
  print_list
    (fun ppf (key, value) ->
      Format.fprintf ppf "@[<hov 1>%a ->@ %a@]" print_key key print_value value)
    ppf bindings

let rec print ppf (t : MT.flambda_type) =
  match t with
  | Type_value ty ->
    Format.fprintf ppf "@[<hov 1>(Value@ %a)@]"
      (print_descr print_head_of_kind_value)
      ty
  | Type_naked_immediate ty ->
    Format.fprintf ppf "@[<hov 1>(Naked_immediate@ %a)@]"
      (print_descr (fun ppf (head : MT.head_of_kind_naked_immediate) ->
           Format.fprintf ppf "@[<hov 1>(%a@ %a)@]"
             (print_or_unknown (print_list N.print_z))
             head.naked_immediates
             (print_list (fun ppf (relation, name) ->
                  Format.fprintf ppf "%a %a" print_relation relation print_name
                    name))
             head.inverse_relations))
      ty
  | Type_naked_number (kind, ty) ->
    Format.fprintf ppf "@[<hov 1>(Naked_number %a@ %a)@]"
      print_naked_number_kind kind
      (print_descr (print_list N.print_z))
      ty
  | Type_rec_info ty ->
    Format.fprintf ppf "@[<hov 1>(Rec_info@ %a)@]"
      (print_descr (fun ppf () -> Format.pp_print_string ppf "()"))
      ty
  | Type_region ty ->
    Format.fprintf ppf "@[<hov 1>(Region@ %a)@]"
      (print_descr (fun ppf () -> Format.pp_print_string ppf "()"))
      ty

and print_head_of_kind_value ppf
    (Head_of_kind_value (non_null, is_null) : MT.head_of_kind_value) =
  Format.fprintf ppf "@[<hov 1>(%t@ %t)@]"
    (fun ppf ->
      match non_null with
      | Unknown -> Format.pp_print_string ppf "Unknown"
      | Bottom -> Format.pp_print_string ppf "Bottom"
      | Ok head -> print_head_of_kind_value_non_null ppf head)
    (fun ppf ->
      match is_null with
      | Not_null -> Format.pp_print_string ppf "Not_null"
      | Maybe_null is_null ->
        Format.fprintf ppf "(Maybe_null %a)"
          (print_option print_variable)
          is_null)

and print_head_of_kind_value_non_null ppf
    (head : MT.head_of_kind_value_non_null) =
  match head with
  | Variant (is_int, immediates, get_tag, blocks, extensions, is_unique) ->
    Format.fprintf ppf
      "@[<hov 1>(Variant@ (is_int %a)@ (immediates %a)@ (get_tag %a)@ (blocks \
       %a)@ (extensions %t)@ (is_unique %b))@]"
      (print_option print_variable)
      is_int (print_or_unknown print) immediates
      (print_option print_variable)
      get_tag
      (print_or_unknown print_row_like_for_blocks)
      blocks
      (fun ppf ->
        match extensions with
        | No_extensions -> Format.pp_print_string ppf "No_extensions"
        | Ext (when_immediate, when_block) ->
          Format.fprintf ppf
            "@[<hov 1>(Ext@ (when_immediate %a)@ (when_block %a))@]"
            print_env_extension when_immediate print_env_extension when_block)
      is_unique
  | Mutable_block alloc_mode ->
    Format.fprintf ppf "(Mutable_block %a)" print_alloc_mode alloc_mode
  | Boxed_number (number, contents, alloc_mode) ->
    (* The number boxed is shown as the kind of what is in the box. *)
    Format.fprintf ppf "@[<hov 1>(Boxed_number %a@ %a@ %a)@]" print_kind
      (MK.unboxed_kind number) print contents print_alloc_mode alloc_mode
  | Closures (Row_like_for_closures known_closures, alloc_mode) ->
    Format.fprintf ppf "@[<hov 1>(Closures@ %a@ %a)@]"
      (print_map N.print_positive
         (fun ppf (case : (_, _, _, _) MT.row_like_case) ->
           Format.fprintf ppf "@[<hov 1>(%a@ %a@ %a)@]"
             (print_index_domain
                (fun ppf (contents : MT.set_of_closures_contents) ->
                  Format.fprintf ppf "@[<hov 1>(closures %a@ value_slots %a)@]"
                    (print_list N.print_positive)
                    contents.contents_closures
                    (print_list N.print_positive)
                    contents.contents_value_slots))
             case.case_index.index_domain print_closures_entry case.case_maps_to
             print_env_extension case.case_env_extension))
      known_closures print_alloc_mode alloc_mode
  | String strs ->
    Format.fprintf ppf "@[<hov 1>(String@ %a)@]"
      (print_list (print_list N.print_z))
      strs

and print_block_case ppf (case : MT.row_like_block_case) =
  Format.fprintf ppf "@[<hov 1>(%a@ %a@ %a@ %a)@]"
    (print_index_domain N.print_nat)
    case.case_index.index_domain print_block_shape case.case_index.index_shape
    (print_list print) case.case_maps_to print_env_extension
    case.case_env_extension

and print_row_like_for_blocks ppf
    (Row_like_for_blocks (known_tags, other_tags, alloc_mode) :
      MT.row_like_for_blocks) =
  Format.fprintf ppf
    "@[<hov 1>((known_tags %a)@ (other_tags %a)@ (alloc_mode %a))@]"
    (print_map N.print_z (print_or_unknown print_block_case))
    known_tags
    (print_or_bottom print_block_case)
    other_tags print_alloc_mode alloc_mode

and print_closures_entry ppf
    (Closures_entry (function_types, closure_types, value_slot_types) :
      MT.closures_entry) =
  Format.fprintf ppf
    "@[<hov 1>((function_types %a)@ (closure_types %a)@ (value_slot_types \
     %a))@]"
    (print_map N.print_positive
       (print_or_unknown
          (fun ppf ({ function_type_code_id = code_id } : MT.function_type) ->
            Format.fprintf ppf "code%a" N.print_positive code_id)))
    function_types
    (print_map N.print_positive print)
    closure_types
    (print_map N.print_positive print)
    value_slot_types

and print_env_extension ppf (Env_extension equations : MT.env_extension) =
  print_map print_name print ppf equations
