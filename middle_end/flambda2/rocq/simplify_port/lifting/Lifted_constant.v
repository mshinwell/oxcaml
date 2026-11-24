(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2021 OCamlPro SAS                                    *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/lifting/lifted_constant.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md; the Rocq form of
   the type [descr] and its extraction directive are in the form of decl/
   for a variant with inline records; the module is [Definition_] because
   [Definition] is a word of Rocq, and the last line of the extracted file
   gives it the compiler's name. No proof. *)

From SimplifyPort Require Import Port_monad.
(* The compiler's file does not open [Simplify_import], which uses it: the
   declarations of that module are not loaded here. *)
From SimplifyPort.decl Require Bound_static Code_id Flambda2_types
  Flambda_kind Format Function_slot List ListLabels Name_mode
  Name_occurrences Rebuilt_static_const Simple Stdlib_ Symbol
  Symbol_projection Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 17 *)
From SimplifyPort.abbrev.lifted_constant Require Import Port_abbreviations.
(*OCAML
module T = Flambda2_types
OCAML*)

(* 19-137 *)
Module Definition_.
  (* 20-33 *)
  (* PORT-GAP(type): the constructors [Set_of_closures] and [Block_like]
     have inline records: the fields are by place, in the order of the
     type, and the directive gives the match. The type is [descr_] in Rocq
     because [descr] is a field of [t] and the function that reads it. *)
  Inductive descr_ : Type :=
  | Code : Code_id.t -> descr_
  | Set_of_closures :
      Flambda2_types.Typing_env.t ->
      Function_slot.Lmap.t (Symbol.t * Flambda2_types.t) ->
      Variable_.Map.t Symbol_projection.t -> descr_
  | Block_like :
      Symbol.t -> Flambda2_types.Typing_env.t -> Flambda2_types.t ->
      Variable_.Map.t Symbol_projection.t -> descr_.
  Extract Inductive descr_ => "descr" [ "Code" "(fun (x__1, x__2, x__3) -> Set_of_closures { typing_env = x__1; closure_symbols_with_types = x__2; symbol_projections = x__3 })" "(fun (x__1, x__2, x__3, x__4) -> Block_like { symbol = x__1; typing_env = x__2; ty = x__3; symbol_projections = x__4 })" ] "(fun f__1 f__2 f__3 x__0 -> match x__0 with Code x__1 -> f__1 x__1 | Set_of_closures { typing_env = x__1; closure_symbols_with_types = x__2; symbol_projections = x__3 } -> f__2 x__1 x__2 x__3 | Block_like { symbol = x__1; typing_env = x__2; ty = x__3; symbol_projections = x__4 } -> f__3 x__1 x__2 x__3 x__4)".
  (* PORT-GAP(verbatim): 20-33, the compiler's definition of [descr] is the
     text of this abbreviation, which Rocq prints at this place, inside the
     module, as [type descr_definition = descr and descr = ...]. The name
     [descr] cannot be the abbreviation's: in Rocq it is the field. *)
  Definition descr_definition : Type := descr_.
  Extract Constant descr_definition => "descr

  and descr =
    | Code of Code_id.t
    | Set_of_closures of
        { typing_env : Typing_env.t;
          closure_symbols_with_types :
            (Symbol.t * Flambda2_types.t) Function_slot.Lmap.t;
          symbol_projections : Symbol_projection.t Variable.Map.t
        }
    | Block_like of
        { symbol : Symbol.t;
          typing_env : Typing_env.t;
          ty : Flambda2_types.t;
          symbol_projections : Symbol_projection.t Variable.Map.t
        }".

  (* 35-38 *)
  (* PORT-GAP(loose): 85 and 87, the functions [descr] and [defining_expr]
     only read the field of their name: they are the projections of this
     record, which Rocq prints here and not at their lines. *)
  Record t : Type := {
    descr : descr_;
    defining_expr : Rebuilt_static_const.t
  }.

  (* 40-47 *)
  Definition binds_symbol (t : Definition_.t) (sym : Symbol.t) : M bool :=
    match t.(descr) with
    | Code _ => ret false
    | Set_of_closures _ closure_symbols_with_types _ =>
      Function_slot.Lmap.exists_
        (fun _ '(sym', _) => Symbol.equal sym sym')
        closure_symbols_with_types
    | Block_like symbol _ _ _ => Symbol.equal sym symbol
    end.

  (* 49-63 *)
  Definition free_names (t : Definition_.t) : M Name_occurrences.t :=
    match t.(descr) with
    | Code _ => Rebuilt_static_const.free_names t.(defining_expr)
    | Set_of_closures _ _ symbol_projections
    | Block_like _ _ _ symbol_projections =>
      (* The symbols mentioned in any symbol projections must be counted as
         free names, so that the definition doesn't get placed too high in
         the code. *)
      let! tmp1 := Rebuilt_static_const.free_names t.(defining_expr) in
      Variable_.Map.fold
        (fun _var proj free_names =>
          let! tmp2 := Symbol_projection.symbol proj in
          Name_occurrences.add_symbol free_names tmp2 Name_mode.normal)
        symbol_projections tmp1
    end.

  (* 65-75 *)
  Definition print_descr (ppf : Format.formatter) (descr : descr_)
      : M unit :=
    match descr with
    | Code code_id => Code_id.print ppf code_id
    | Set_of_closures _ closure_symbols_with_types _ =>
      (* 69-71: [a |> f b] is [f b a]. *)
      let* symbols :=
        let! tmp1 := Function_slot.Lmap.data closure_symbols_with_types in
        List.map Stdlib_.fst tmp1
      in
      (* PORT-GAP(papp): [Format.pp_print_list] is given its first two
         arguments only. *)
      let! tmp1 :=
        papp2 Format.pp_print_list (Some Format.pp_print_space) Symbol.print
      in
      Format.fprintf2 ppf "@[<hov 1>(%a)@]" tmp1 symbols
    | Block_like symbol _ _ _ => Symbol.print ppf symbol
    end.

  (* 77-83 *)
  (* PORT-GAP(loose): 77, the attribute [@ocamlformat "disable"] is not
     kept; the lines of the format are joined. *)
  Definition print (ppf : Format.formatter)
      '({| descr := descr; defining_expr := defining_expr |} : Definition_.t)
      : M unit :=
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(descr@ %a)@]@ @[<hov 1>(defining_expr@ %a)@]@]"
      print_descr descr Rebuilt_static_const.print defining_expr.

  (* 85: [descr], and 87: [defining_expr], are the projections above. *)

  (* 89-94 *)
  Definition symbol_projections (t : Definition_.t)
      : M (Variable_.Map.t Symbol_projection.t) :=
    match t.(descr) with
    | Code _ => ret Variable_.Map.empty
    | Set_of_closures _ _ symbol_projections
    | Block_like _ _ _ symbol_projections =>
      ret symbol_projections
    end.

  (* 96 *)
  Definition code (code_id : Code_id.t)
      (defining_expr : Rebuilt_static_const.t) : M t :=
    ret {| descr := Code code_id; defining_expr := defining_expr |}.

  (* 98-104. In the compiler: [typing_env ~closure_symbols_with_types
     ~symbol_projections defining_expr]. *)
  Definition set_of_closures (typing_env : Flambda2_types.Typing_env.t)
      (closure_symbols_with_types :
        Function_slot.Lmap.t (Symbol.t * Flambda2_types.t))
      (symbol_projections : Variable_.Map.t Symbol_projection.t)
      (defining_expr : Rebuilt_static_const.t) : M t :=
    ret
      {| descr :=
           Set_of_closures typing_env closure_symbols_with_types
             symbol_projections;
         defining_expr := defining_expr
      |}.

  (* 106-109. In the compiler: [typing_env symbol ty ~symbol_projections
     defining_expr]. *)
  Definition block_like (typing_env : Flambda2_types.Typing_env.t)
      (symbol : Symbol.t) (ty : Flambda2_types.t)
      (symbol_projections : Variable_.Map.t Symbol_projection.t)
      (defining_expr : Rebuilt_static_const.t) : M t :=
    ret
      {| descr := Block_like symbol typing_env ty symbol_projections;
         defining_expr := defining_expr
      |}.

  (* 111-115 *)
  Definition typing_env (t : Definition_.t)
      : M (option Flambda2_types.Typing_env.t) :=
    match t.(descr) with
    | Code _ => ret None
    | Set_of_closures typing_env _ _ | Block_like _ typing_env _ _ =>
      ret (Some typing_env)
    end.

  (* 117-123 *)
  Definition bound_static_pattern (t : Definition_.t)
      : M Bound_static.Pattern.t :=
    (* PORT-GAP(loose): 118, [let module P = Bound_static.Pattern in] is not
       kept: the functions of [P] are written [Bound_static.Pattern.f]. *)
    match t.(descr) with
    | Code code_id => Bound_static.Pattern.code code_id
    | Set_of_closures _ closure_symbols_with_types _ =>
      let! tmp1 :=
        Function_slot.Lmap.map Stdlib_.fst closure_symbols_with_types
      in
      Bound_static.Pattern.set_of_closures tmp1
    | Block_like symbol _ _ _ => Bound_static.Pattern.block_like symbol
    end.

  (* 125 *)
  Definition bound_static (t : Definition_.t) : M Bound_static.t :=
    let! tmp1 := bound_static_pattern t in
    Bound_static.create [tmp1].

  (* 127-136 *)
  Definition types_of_symbols (t : Definition_.t)
      : M (Symbol.Map.t (Flambda2_types.Typing_env.t * Flambda2_types.t)) :=
    match t.(descr) with
    | Code _ => ret Symbol.Map.empty
    | Set_of_closures typing_env closure_symbols_with_types _ =>
      Function_slot.Lmap.fold
        (fun _function_slot '(symbol, ty) types_of_symbols =>
          Symbol.Map.add symbol (typing_env, ty) types_of_symbols)
        closure_symbols_with_types Symbol.Map.empty
    | Block_like symbol typing_env ty _ =>
      Symbol.Map.singleton symbol (typing_env, ty)
    end.
End Definition_.

(* 139-145 *)
(* PORT-GAP(type): the fields [bound_static] and [defining_exprs] have the
   names of two functions of the file (lines 263 and 267) that do NOT read
   them: in Rocq the two fields are [bound_static_] and [defining_exprs_],
   and their directives make Rocq print the compiler's names for them in
   the type, in a record and in a pattern. Such a field is READ by a match
   ([match t with {| defining_exprs_ := x |} => x end], which Rocq prints
   [t.defining_exprs]): for [t.(defining_exprs_)] Rocq would print the call
   [defining_exprs t], which is the function of line 263. *)
(* PORT-GAP(loose): 147, 149 and 154, the functions [definitions],
   [symbol_projections] and [is_fully_static] only read the field of their
   name: they are the projections of this record, which Rocq prints here. *)
Record t : Type := {
  definitions : list Definition_.t;
  bound_static_ : Bound_static.t;
  defining_exprs_ : Rebuilt_static_const.Group.t;
  symbol_projections : Variable_.Map.t Symbol_projection.t;
  is_fully_static : bool
}.
Extract Inlined Constant bound_static_ => "bound_static".
Extract Inlined Constant defining_exprs_ => "defining_exprs".

(* 147: [definitions], and 149: [symbol_projections], are the projections
   above. *)

(* 151-152 *)
Definition free_names_of_defining_exprs (t : Lifted_constant.t)
    : M Name_occurrences.t :=
  Rebuilt_static_const.Group.free_names
    (match t with {| defining_exprs_ := x |} => x end).

(* 154: [is_fully_static] is the projection above. *)

(* 156-161 *)
(* PORT-GAP(loose): 156, the attribute [@ocamlformat "disable"] is not
   kept. *)
Definition print (ppf : Format.formatter)
    '({| definitions := definitions;
         bound_static_ := _;
         defining_exprs_ := _;
         symbol_projections := _;
         is_fully_static := _
      |} : Lifted_constant.t) : M unit :=
  (* PORT-GAP(papp): [Format.pp_print_list] is given its first two arguments
     only. *)
  let! tmp1 :=
    papp2 Format.pp_print_list (Some Format.pp_print_space) Definition_.print
  in
  Format.fprintf2 ppf "@[<hov 1>(%a)@]" tmp1 definitions.

(* 163-165: [a |> f b] is [f b a]; [ListLabels.map l ~f]: the arguments are
   in the order of the interface. *)
Definition compute_bound_static (definitions : list Definition_.t)
    : M Bound_static.t :=
  let! tmp1 := ListLabels.map Definition_.bound_static_pattern definitions in
  Bound_static.create tmp1.

(* 167-169 *)
Definition compute_defining_exprs (definitions : list Definition_.t)
    : M Rebuilt_static_const.Group.t :=
  (* PORT-GAP(loose): 168, [~f:Definition.defining_expr]: the function is a
     projection, which is not in [M]: it is written out. *)
  let! tmp1 :=
    ListLabels.map
      (fun definition => ret definition.(Definition_.defining_expr))
      definitions
  in
  Rebuilt_static_const.Group.create tmp1.

(* 171-185. In the compiler: [symbol ~symbol_projections defining_expr denv
   ty]. *)
Definition create_block_like (symbol : Symbol.t)
    (symbol_projections : Variable_.Map.t Symbol_projection.t)
    (defining_expr : Rebuilt_static_const.t)
    (denv : Flambda2_types.Typing_env.t) (ty : Flambda2_types.t) : M t :=
  (let! tmp1 := Rebuilt_static_const.is_block defining_expr in
   if negb tmp1
   then
     fatal_errorf2 "Defining expression must be a block:@ %a"
       Rebuilt_static_const.print defining_expr
   else ret tt) ;;
  let* definition :=
    Definition_.block_like denv symbol ty symbol_projections defining_expr
  in
  let& definitions := [definition] in
  (* PORT-GAP(record-order): 180-185, four fields of the record are calls:
     each is bound before the record, in the order of the type, the last
     field first. *)
  let* is_fully_static :=
    Rebuilt_static_const.is_fully_static defining_expr
  in
  let* symbol_projections := Definition_.symbol_projections definition in
  let* defining_exprs := compute_defining_exprs definitions in
  let* bound_static := compute_bound_static definitions in
  ret
    {| Lifted_constant.definitions := definitions;
       bound_static_ := bound_static;
       defining_exprs_ := defining_exprs;
       Lifted_constant.symbol_projections := symbol_projections;
       Lifted_constant.is_fully_static := is_fully_static
    |}.

(* 187-203. In the compiler: [denv ~closure_symbols_with_types
   ~symbol_projections defining_expr]. *)
Definition create_set_of_closures (denv : Flambda2_types.Typing_env.t)
    (closure_symbols_with_types :
      Function_slot.Lmap.t (Symbol.t * Flambda2_types.t))
    (symbol_projections : Variable_.Map.t Symbol_projection.t)
    (defining_expr : Rebuilt_static_const.t) : M t :=
  (let! tmp1 := Rebuilt_static_const.is_set_of_closures defining_expr in
   if negb tmp1
   then
     fatal_errorf2 "Defining expression must be a set of closures:@ %a"
       Rebuilt_static_const.print defining_expr
   else ret tt) ;;
  let* definition :=
    Definition_.set_of_closures denv closure_symbols_with_types
      symbol_projections defining_expr
  in
  let& definitions := [definition] in
  (* PORT-GAP(record-order): 198-203, four fields of the record are calls:
     each is bound before the record, in the order of the type, the last
     field first. *)
  let* is_fully_static :=
    Rebuilt_static_const.is_fully_static defining_expr
  in
  let* symbol_projections := Definition_.symbol_projections definition in
  let* defining_exprs := compute_defining_exprs definitions in
  let* bound_static := compute_bound_static definitions in
  ret
    {| Lifted_constant.definitions := definitions;
       bound_static_ := bound_static;
       defining_exprs_ := defining_exprs;
       Lifted_constant.symbol_projections := symbol_projections;
       Lifted_constant.is_fully_static := is_fully_static
    |}.

(* 205-217 *)
Definition create_code (code_id : Code_id.t)
    (defining_expr : Rebuilt_static_const.t) : M t :=
  (let! tmp1 := Rebuilt_static_const.is_code defining_expr in
   if negb tmp1
   then
     fatal_errorf2 "Defining expression must be code:@ %a"
       Rebuilt_static_const.print defining_expr
   else ret tt) ;;
  let* definition := Definition_.code code_id defining_expr in
  let& definitions := [definition] in
  (* PORT-GAP(record-order): 212-217, four fields of the record are calls:
     each is bound before the record, in the order of the type, the last
     field first. *)
  let* is_fully_static :=
    Rebuilt_static_const.is_fully_static defining_expr
  in
  let* symbol_projections := Definition_.symbol_projections definition in
  let* defining_exprs := compute_defining_exprs definitions in
  let* bound_static := compute_bound_static definitions in
  ret
    {| Lifted_constant.definitions := definitions;
       bound_static_ := bound_static;
       defining_exprs_ := defining_exprs;
       Lifted_constant.symbol_projections := symbol_projections;
       Lifted_constant.is_fully_static := is_fully_static
    |}.

(* 219-227 *)
Definition create_definition (definition : Definition_.t) : M t :=
  let& definitions := [definition] in
  (* PORT-GAP(record-order): 221-227, four fields of the record are calls:
     each is bound before the record, in the order of the type, the last
     field first. 225: [Definition.defining_expr definition] is the
     projection. *)
  let* is_fully_static :=
    Rebuilt_static_const.is_fully_static
      definition.(Definition_.defining_expr)
  in
  let* symbol_projections := Definition_.symbol_projections definition in
  let* defining_exprs := compute_defining_exprs definitions in
  let* bound_static := compute_bound_static definitions in
  ret
    {| Lifted_constant.definitions := definitions;
       bound_static_ := bound_static;
       defining_exprs_ := defining_exprs;
       Lifted_constant.symbol_projections := symbol_projections;
       Lifted_constant.is_fully_static := is_fully_static
    |}.

(* 229-261 *)
Definition concat (ts : list t) : M t :=
  let* definitions :=
    List.fold_left
      (fun definitions t =>
        ret (t.(Lifted_constant.definitions) ++ definitions))
      [] ts
  in
  let* bound_static :=
    List.fold_left
      (fun bound_static t =>
        Bound_static.concat
          (match t with {| bound_static_ := x |} => x end)
          bound_static)
      Bound_static.empty ts
  in
  let* defining_exprs :=
    List.fold_left
      (fun defining_exprs t =>
        Rebuilt_static_const.Group.concat
          (match t with {| defining_exprs_ := x |} => x end)
          defining_exprs)
      Rebuilt_static_const.Group.empty ts
  in
  let* is_fully_static :=
    List.fold_left
      (fun is_fully_static t =>
        ret (t.(Lifted_constant.is_fully_static) && is_fully_static))
      true ts
  in
  let* symbol_projections :=
    List.fold_left
      (fun symbol_projections t =>
        Variable_.Map.disjoint_union (Some Symbol_projection.equal) None
          t.(Lifted_constant.symbol_projections) symbol_projections)
      Variable_.Map.empty ts
  in
  ret
    {| Lifted_constant.definitions := definitions;
       bound_static_ := bound_static;
       defining_exprs_ := defining_exprs;
       Lifted_constant.symbol_projections := symbol_projections;
       Lifted_constant.is_fully_static := is_fully_static
    |}.

(* 263-265 *)
Definition defining_exprs (t : Lifted_constant.t)
    : M Rebuilt_static_const.Group.t :=
  (* PORT-GAP(loose): 265, [List.map Definition.defining_expr]: the function
     is a projection, which is not in [M]: it is written out. *)
  let! tmp1 :=
    List.map
      (fun definition => ret definition.(Definition_.defining_expr))
      t.(definitions)
  in
  Rebuilt_static_const.Group.create tmp1.

(* 267-268 *)
Definition bound_static (t : Lifted_constant.t) : M Bound_static.t :=
  let! tmp1 := List.map Definition_.bound_static_pattern t.(definitions) in
  Bound_static.create tmp1.

(* 270-275. [ListLabels.fold_left l ~init ~f]: the arguments are in the
   order of the interface. *)
Definition types_of_symbols (t : Lifted_constant.t)
    : M (Symbol.Map.t (Flambda2_types.Typing_env.t * Flambda2_types.t)) :=
  ListLabels.fold_left
    (fun types_of_symbols definition =>
      let! tmp1 := Definition_.types_of_symbols definition in
      Symbol.Map.disjoint_union None None tmp1 types_of_symbols)
    Symbol.Map.empty t.(definitions).

(* 277 *)
Definition all_defined_symbols (t : Lifted_constant.t)
    : M Symbol.Map.Set_.t :=
  let! tmp1 := types_of_symbols t in
  Symbol.Map.keys tmp1.

(* 279-324 *)
Definition apply_projection (t : Lifted_constant.t)
    (proj : Symbol_projection.t) : M (option Simple.t) :=
  let* symbol := Symbol_projection.symbol proj in
  (* 281-286, [ListLabels.filter_map l ~f]: the arguments are in the order
     of the interface. *)
  let* matching_defining_exprs :=
    ListLabels.filter_map
      (fun definition =>
        let! tmp1 := Definition_.binds_symbol definition symbol in
        if tmp1 then ret (Some definition) else ret None)
      t.(definitions)
  in
  match matching_defining_exprs with
  | [matched_defining_expr] =>
    (* 289-291 *)
    let* '(typing_env, ty) :=
      let! tmp1 := Definition_.types_of_symbols matched_defining_expr in
      Symbol.Map.find symbol tmp1
    in
    (* 292-303 *)
    let* meet_shortcut :=
      let! tmp1 := Symbol_projection.projection proj in
      match tmp1 with
      | Symbol_projection.Projection.Block_load index _ =>
        let* field_kind :=
          let! tmp1 := Symbol_projection.kind proj in
          Flambda_kind.With_subkind.kind tmp1
        in
        T.meet_block_field_simple typing_env Name_mode.normal field_kind ty
          index
      | Symbol_projection.Projection.Project_value_slot _ value_slot =>
        T.meet_project_value_slot_simple typing_env Name_mode.normal ty
          value_slot
      end
    in
    (* 304-319 *)
    match meet_shortcut with
    | T.Known_result simple => ret (Some simple)
    | T.Need_meet =>
      (* [Simplify_named], which calls this function, requires [Some] to be
         returned if the projection is from a symbol defined in the same
         recursive group (see the comment in that module). As such, if the
         projection via the types fails, we currently stop. It seems very
         unlikely that this will happen; we can reconsider in the future if
         necessary. *)
      fatal_errorf6
        "Symbol projection@ %a@ produced [Need_meet]:@ type is@ %a@ in env:@ %a"
        Symbol_projection.print proj T.print ty T.Typing_env.print typing_env
    | T.Invalid =>
      fatal_errorf4
        "Symbol projection@ %a@ produced [Invalid],@ environment is:@ %a"
        Symbol_projection.print proj T.Typing_env.print typing_env
    end
  | [] => ret None
  | _ :: _ :: _ =>
    fatal_errorf4
      "Symbol projection@ %a@ matches more than one constant in:@ %a"
      Symbol_projection.print proj print t
  end.

(*OCAML-END
module Definition = Definition_
OCAML-END*)
