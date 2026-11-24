(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/flow/flow_acc.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter
  Bound_parameters Bound_pattern Bound_static Bound_var Code_id Continuation
  Continuation_callsite_map Continuation_extra_params_and_args
  Exn_continuation Flambda Flambda2_types Flambda_arity Flambda_kind
  Flambda_primitive Flow_types Format Function_declarations Function_slot
  Lifted_constant Lifted_constant_state List ListLabels Name Name_mode
  Name_occurrences Named_rewrite_id Numeric_types Option Or_invalid Or_null
  Rebuilt_static_const Set_of_closures Simple Simplified_named Static_const
  Symbol Symbol_projection Target_ocaml_int Value_slot Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda.static_const_or_code
   Flambda_primitive.t Flambda_primitive.unary_primitive
   Flambda_primitive.variadic_primitive Flow_types.Mutable_prim.t
   Lifted_constant.Definition_.descr_ Or_null.t
   Simplified_named.simplified_named *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
From SimplifyPort.abbrev.flow_acc Require Import Port_abbreviations.
(*OCAML
module T = Flow_types
module EPA = Continuation_extra_params_and_args
OCAML*)

(* 16 *)

(* 18 *)
Definition t : Type := T.Acc.t.

(* 20 *)
Definition cont_info : Type := T.Continuation_info.t.

(* 22 *)
Definition print : Format.formatter -> Flow_acc.t -> M unit := T.Acc.print.

(* Creation *)
(* ******** *)

(* 27 *)
Definition wrong_dummy_toplevel_cont_name : string := "wrong toplevel cont".

(* 29-41 *)
Definition empty (_ : unit) : M Flow_acc.t :=
  let* wrong_dummy_toplevel_cont :=
    Continuation.create None (Some wrong_dummy_toplevel_cont_name) tt
  in
  let& res :=
    {| T.Acc.stack := [];
       T.Acc.map := Continuation.Map.empty;
       T.Acc.extra := Continuation.Map.empty;
       T.Acc.lifted_constants := Lifted_constant_state.empty;
       T.Acc.dummy_toplevel_cont := wrong_dummy_toplevel_cont
    |}
  in
  ret res.

(* Updates *)
(* ******* *)

(* PORT-GAP(update): 54, [{ t with extra }]. *)
Definition update_extra (t : T.Acc.t)
    (extra : Continuation.Map.t Continuation_extra_params_and_args.t)
    : T.Acc.t :=
  {| T.Acc.stack := t.(Flow_types.Acc.stack);
     T.Acc.map := t.(Flow_types.Acc.map);
     T.Acc.extra := extra;
     T.Acc.lifted_constants := t.(Flow_types.Acc.lifted_constants);
     T.Acc.dummy_toplevel_cont := t.(Flow_types.Acc.dummy_toplevel_cont)
  |}.
Extract Inlined Constant update_extra =>
  "(fun t extra -> { t with T.Acc.extra = extra })".

(* 46-54 *)
Definition add_extra_params_and_args (cont : Continuation.t)
    (extra : Continuation_extra_params_and_args.t) (t : Flow_acc.t)
    : M Flow_acc.t :=
  let* extra :=
    Continuation.Map.update cont
      (fun x =>
        match x with
        | Some _ => fatal_errorf0 "Continuation extended a second time"
        | None => ret (Some extra)
        end)
      t.(Flow_types.Acc.extra)
  in
  ret (update_extra t extra).

(* PORT-GAP(update): 86, 104, [{ t with stack }]. *)
Definition update_stack (t : T.Acc.t) (stack : list T.Continuation_info.t)
    : T.Acc.t :=
  {| T.Acc.stack := stack;
     T.Acc.map := t.(Flow_types.Acc.map);
     T.Acc.extra := t.(Flow_types.Acc.extra);
     T.Acc.lifted_constants := t.(Flow_types.Acc.lifted_constants);
     T.Acc.dummy_toplevel_cont := t.(Flow_types.Acc.dummy_toplevel_cont)
  |}.
Extract Inlined Constant update_stack =>
  "(fun t stack -> { t with T.Acc.stack = stack })".

(* 56-86 *)
Definition enter_continuation (continuation : Continuation.t)
    (recursive is_exn_handler : bool) (params : Bound_parameters.t)
    (t : Flow_acc.t) : M Flow_acc.t :=
  let& parent_continuation :=
    match t.(Flow_types.Acc.stack) with
    | [] => None
    | parent :: _ => Some parent.(Flow_types.Continuation_info.continuation)
    end
  in
  let* used_in_handler :=
    if negb is_exn_handler
    then ret Name_occurrences.empty
    else
      (* The first param of an exn_handler is unconditionally used *)
      let* first_param :=
        let! tmp1 := Bound_parameters.to_list params in
        let! tmp2 := List.hd tmp1 in
        Bound_parameter.var tmp2
      in
      Name_occurrences.singleton_variable first_param Name_mode.normal
  in
  let& cont_info :=
    {| T.Continuation_info.continuation := continuation;
       T.Continuation_info.recursive := recursive;
       T.Continuation_info.is_exn_handler := is_exn_handler;
       T.Continuation_info.params := params;
       T.Continuation_info.parent_continuation := parent_continuation;
       T.Continuation_info.bindings := Name.Map.empty;
       T.Continuation_info.direct_aliases := Variable_.Map.empty;
       T.Continuation_info.mutable_let_prims_rev := [];
       T.Continuation_info.defined := Variable_.Set_.empty;
       T.Continuation_info.code_ids := Code_id.Map.empty;
       T.Continuation_info.value_slots := Value_slot.Map.empty;
       T.Continuation_info.used_in_handler := used_in_handler;
       T.Continuation_info.apply_cont_args := Continuation.Map.empty
    |}
  in
  ret (update_stack t (cont_info :: t.(Flow_types.Acc.stack))).

(* PORT-GAP(update): 91, [{ (empty ()) with dummy_toplevel_cont }]. *)
Definition update_dummy_toplevel_cont (t : T.Acc.t)
    (dummy_toplevel_cont : Continuation.t) : T.Acc.t :=
  {| T.Acc.stack := t.(Flow_types.Acc.stack);
     T.Acc.map := t.(Flow_types.Acc.map);
     T.Acc.extra := t.(Flow_types.Acc.extra);
     T.Acc.lifted_constants := t.(Flow_types.Acc.lifted_constants);
     T.Acc.dummy_toplevel_cont := dummy_toplevel_cont
  |}.
Extract Inlined Constant update_dummy_toplevel_cont =>
  "(fun t dummy_toplevel_cont -> { t with T.Acc.dummy_toplevel_cont =
   dummy_toplevel_cont })".

(* 88-91 *)
Definition init_toplevel (dummy_toplevel_cont : Continuation.t)
    (params : Bound_parameters.t) : M Flow_acc.t :=
  let! tmp1 := empty tt in
  enter_continuation dummy_toplevel_cont false false params
    (update_dummy_toplevel_cont tmp1 dummy_toplevel_cont).

(* PORT-GAP(update): 99, [{ t with stack; map }]. *)
Definition update_stack_map (t : T.Acc.t) (stack : list T.Continuation_info.t)
    (map : Continuation.Map.t T.Continuation_info.t) : T.Acc.t :=
  {| T.Acc.stack := stack;
     T.Acc.map := map;
     T.Acc.extra := t.(Flow_types.Acc.extra);
     T.Acc.lifted_constants := t.(Flow_types.Acc.lifted_constants);
     T.Acc.dummy_toplevel_cont := t.(Flow_types.Acc.dummy_toplevel_cont)
  |}.
Extract Inlined Constant update_stack_map =>
  "(fun t stack map -> { t with T.Acc.stack = stack; map = map })".

(* 93-99 *)
Definition exit_continuation (cont : Continuation.t) (t : Flow_acc.t)
    : M Flow_acc.t :=
  match t.(Flow_types.Acc.stack) with
  | [] => fatal_errorf0 "Empty stack of variable uses"
  | elt :: stack =>
    (* 96: [({ continuation; _ } as elt) :: stack] *)
    let* '{| T.Continuation_info.continuation := continuation |} := ret elt in
    (let! tmp1 := Continuation.equal cont continuation in
     assert_ tmp1) ;;
    let* map := Continuation.Map.add cont elt t.(Flow_types.Acc.map) in
    ret (update_stack_map t stack map)
  end.

(* 101-104. In the compiler: [~t ~f]. *)
Definition update_top_of_stack (t : Flow_acc.t)
    (f : cont_info -> M cont_info) : M Flow_acc.t :=
  match t.(Flow_types.Acc.stack) with
  | [] => fatal_errorf0 "Empty stack of variable uses"
  | elt :: stack =>
    let! tmp1 := f elt in
    ret (update_stack t (tmp1 :: stack))
  end.

(* PORT-GAP(update): 109, 612, [{ elt with defined }]. *)
Definition update_defined (t : T.Continuation_info.t)
    (defined : Variable_.Set_.t) : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := defined;
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_defined =>
  "(fun t defined -> { t with T.Continuation_info.defined = defined })".

(* 106-109 *)
Definition record_defined_var (var : Variable_.t) (t : Flow_acc.t)
    : M Flow_acc.t :=
  update_top_of_stack t (fun elt =>
    let* defined :=
      Variable_.Set_.add var elt.(Flow_types.Continuation_info.defined)
    in
    ret (update_defined elt defined)).

(* PORT-GAP(update): 131, [{ elt with bindings; used_in_handler; defined }]. *)
Definition update_bindings_used_in_handler_defined (t : T.Continuation_info.t)
    (bindings : Name.Map.t Name_occurrences.t)
    (used_in_handler : Name_occurrences.t) (defined : Variable_.Set_.t)
    : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler := used_in_handler;
     T.Continuation_info.bindings := bindings;
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := defined;
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_bindings_used_in_handler_defined =>
  "(fun t bindings used_in_handler defined -> { t with
   T.Continuation_info.bindings = bindings; used_in_handler = used_in_handler;
   defined = defined })".

(* 111-131 *)
Definition record_var_binding (var : Variable_.t)
    (name_occurrences : Name_occurrences.t) (generate_phantom_lets : bool)
    (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (fun elt =>
    let* bindings :=
      let! tmp1 := Name.var var in
      Name.Map.update tmp1
        (fun x =>
          match x with
          | None => ret (Some name_occurrences)
          | Some _ =>
            fatal_errorf2 "The following variable has been bound twice: %a"
              Variable_.print var
          end)
        elt.(Flow_types.Continuation_info.bindings)
    in
    let* used_in_handler :=
      let! tmp1 := Variable_.user_visible var in
      if tmp1 && generate_phantom_lets
      then
        Name_occurrences.add_variable
          elt.(Flow_types.Continuation_info.used_in_handler) var
          Name_mode.phantom
      else ret elt.(Flow_types.Continuation_info.used_in_handler)
    in
    let* defined :=
      Variable_.Set_.add var elt.(Flow_types.Continuation_info.defined)
    in
    ret
      (update_bindings_used_in_handler_defined elt bindings used_in_handler
        defined)).

(* PORT-GAP(update): 146, [{ elt with direct_aliases; defined }]. *)
Definition update_direct_aliases_defined (t : T.Continuation_info.t)
    (direct_aliases : Variable_.Map.t Simple.t) (defined : Variable_.Set_.t)
    : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases := direct_aliases;
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := defined;
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_direct_aliases_defined =>
  "(fun t direct_aliases defined -> { t with
   T.Continuation_info.direct_aliases = direct_aliases; defined = defined })".

(* 133-146 *)
Definition record_var_alias (var : Variable_.t) (definition : Simple.t)
    (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (fun elt =>
    let* direct_aliases :=
      Variable_.Map.update var
        (fun x =>
          match x with
          | None => ret (Some definition)
          | Some _ =>
            fatal_errorf2 "The following variable has been bound twice: %a"
              Variable_.print var
          end)
        elt.(Flow_types.Continuation_info.direct_aliases)
    in
    let* defined :=
      Variable_.Set_.add var elt.(Flow_types.Continuation_info.defined)
    in
    ret (update_direct_aliases_defined elt direct_aliases defined)).

(* PORT-GAP(update): 156, [{ cont_info with mutable_let_prims_rev }]. *)
Definition update_mutable_let_prims_rev (t : T.Continuation_info.t)
    (mutable_let_prims_rev : T.Mutable_let_prim.List.t)
    : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev := mutable_let_prims_rev;
     T.Continuation_info.defined := t.(Flow_types.Continuation_info.defined);
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_mutable_let_prims_rev =>
  "(fun t mutable_let_prims_rev -> { t with
   T.Continuation_info.mutable_let_prims_rev = mutable_let_prims_rev })".

(* 148-156. In the compiler: [named_rewrite_id ~bound_to ~original_prim ~prim
   t]. *)
Definition record_ref_named (named_rewrite_id : Named_rewrite_id.t)
    (bound_to : Variable_.t) (original_prim : Flambda_primitive.t)
    (prim : T.Mutable_prim.t) (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (fun cont_info =>
    let& mutable_let_prim :=
      {| T.Mutable_let_prim.bound_var := bound_to;
         T.Mutable_let_prim.named_rewrite_id := named_rewrite_id;
         T.Mutable_let_prim.original_prim := original_prim;
         T.Mutable_let_prim.prim := prim
      |}
    in
    let& mutable_let_prims_rev :=
      mutable_let_prim
      :: cont_info.(Flow_types.Continuation_info.mutable_let_prims_rev)
    in
    ret (update_mutable_let_prims_rev cont_info mutable_let_prims_rev)).

(* PORT-GAP(update): 174, 189, [{ elt with bindings }]. *)
Definition update_bindings (t : T.Continuation_info.t)
    (bindings : Name.Map.t Name_occurrences.t) : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := bindings;
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := t.(Flow_types.Continuation_info.defined);
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_bindings =>
  "(fun t bindings -> { t with T.Continuation_info.bindings = bindings })".

(* 158-174 *)
Definition record_symbol_projection_aux (var : Variable_.t)
    (name_occurrences : Name_occurrences.t) (elt : cont_info) : M cont_info :=
  let* bindings :=
    let! tmp1 := Name.var var in
    Name.Map.update tmp1
      (* 163: [Some prior_occurences as original] *)
      (fun original =>
        match original with
        | None => ret (Some name_occurrences)
        | Some prior_occurences =>
          let! tmp2 :=
            Name_occurrences.equal prior_occurences name_occurrences
          in
          if tmp2
          then ret original
          else
            fatal_errorf6
              "@[<v>The following projection has been bound to different symbols:%a@ previously bound to:@ %a@ and now to@ %a@]"
              Variable_.print var Name_occurrences.print prior_occurences
              Name_occurrences.print name_occurrences
        end)
      elt.(Flow_types.Continuation_info.bindings)
  in
  ret (update_bindings elt bindings).

(* 176-177 *)
Definition record_symbol_projection (var : Variable_.t)
    (name_occurrences : Name_occurrences.t) (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (record_symbol_projection_aux var name_occurrences).

(* 179-189 *)
Definition record_symbol_binding_aux (symbol : Symbol.t)
    (name_occurrences : Name_occurrences.t) (elt : cont_info) : M cont_info :=
  let* bindings :=
    let! tmp1 := Name.symbol symbol in
    Name.Map.update tmp1
      (fun x =>
        match x with
        | None => ret (Some name_occurrences)
        | Some _ =>
          fatal_errorf2 "The following symbol has been bound twice: %a"
            Symbol.print symbol
        end)
      elt.(Flow_types.Continuation_info.bindings)
  in
  ret (update_bindings elt bindings).

(* 191-192 *)
Definition record_symbol_binding (symbol : Symbol.t)
    (name_occurrences : Name_occurrences.t) (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (record_symbol_binding_aux symbol name_occurrences).

(* PORT-GAP(update): 204, [{ elt with code_ids }]. *)
Definition update_code_ids (t : T.Continuation_info.t)
    (code_ids : Code_id.Map.t Name_occurrences.t) : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := t.(Flow_types.Continuation_info.defined);
     T.Continuation_info.code_ids := code_ids;
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_code_ids =>
  "(fun t code_ids -> { t with T.Continuation_info.code_ids = code_ids })".

(* 194-204 *)
Definition record_code_id_binding_aux (code_id : Code_id.t)
    (name_occurrences : Name_occurrences.t) (elt : cont_info) : M cont_info :=
  let* code_ids :=
    Code_id.Map.update code_id
      (fun x =>
        match x with
        | None => ret (Some name_occurrences)
        | Some _ =>
          fatal_errorf2 "The following code_id has been bound twice: %a"
            Code_id.print code_id
        end)
      elt.(Flow_types.Continuation_info.code_ids)
  in
  ret (update_code_ids elt code_ids).

(* 206-208 *)
Definition record_code_id_binding (code_id : Code_id.t)
    (name_occurrences : Name_occurrences.t) (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (record_code_id_binding_aux code_id name_occurrences).

(* PORT-GAP(update): 224, [{ elt with value_slots }]. *)
Definition update_value_slots (t : T.Continuation_info.t)
    (value_slots : Value_slot.Map.t (Name.Map.t Name_occurrences.t))
    : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := t.(Flow_types.Continuation_info.defined);
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots := value_slots;
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_value_slots =>
  "(fun t value_slots -> { t with T.Continuation_info.value_slots =
   value_slots })".

(* 210-224 *)
Definition record_value_slot_aux (src : Name.t) (value_slot : Value_slot.t)
    (dst : Name_occurrences.t) (elt : cont_info) : M cont_info :=
  let* value_slots :=
    Value_slot.Map.update value_slot
      (fun x =>
        match x with
        | None =>
          let! tmp1 := Name.Map.singleton src dst in
          ret (Some tmp1)
        | Some map =>
          let! tmp1 :=
            Name.Map.update src
              (fun x =>
                match x with
                | None => ret (Some dst)
                | Some dst' =>
                  let! tmp2 := Name_occurrences.union dst dst' in
                  ret (Some tmp2)
                end)
              map
          in
          ret (Some tmp1)
        end)
      elt.(Flow_types.Continuation_info.value_slots)
  in
  ret (update_value_slots elt value_slots).

(* 226-227 *)
Definition record_value_slot (src : Name.t) (value_slot : Value_slot.t)
    (dst : Name_occurrences.t) (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (record_value_slot_aux src value_slot dst).

(* PORT-GAP(update): 234, [{ elt with used_in_handler }]. *)
Definition update_used_in_handler (t : T.Continuation_info.t)
    (used_in_handler : Name_occurrences.t) : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler := used_in_handler;
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := t.(Flow_types.Continuation_info.defined);
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_used_in_handler =>
  "(fun t used_in_handler -> { t with T.Continuation_info.used_in_handler =
   used_in_handler })".

(* 229-234 *)
Definition add_used_in_current_handler (name_occurrences : Name_occurrences.t)
    (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (fun elt =>
    let* used_in_handler :=
      Name_occurrences.union
        elt.(Flow_types.Continuation_info.used_in_handler) name_occurrences
    in
    ret (update_used_in_handler elt used_in_handler)).

(* PORT-GAP(update): 293, 331, 577, [{ elt with apply_cont_args }]. *)
Definition update_apply_cont_args (t : T.Continuation_info.t)
    (apply_cont_args :
      Continuation_callsite_map.t (Numeric_types.Int.Map.t T.Cont_arg.t))
    : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := t.(Flow_types.Continuation_info.params);
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := t.(Flow_types.Continuation_info.defined);
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args := apply_cont_args
  |}.
Extract Inlined Constant update_apply_cont_args =>
  "(fun t apply_cont_args -> { t with T.Continuation_info.apply_cont_args =
   apply_cont_args })".

(* 236-293 *)
Definition add_apply_conts
    (result_cont : option (Apply_cont_rewrite_id.t * Continuation.t))
    (exn_cont : Apply_cont_rewrite_id.t * Exn_continuation.t)
    (result_arity : Flambda_arity.t) (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (fun elt =>
    (* 238-276. In the compiler: [cont rewrite_id ~result_arity ~extra_args
       apply_cont_args]. *)
    let& add_func_result :=
      fun (cont : Continuation.t) (rewrite_id : Apply_cont_rewrite_id.t)
          (result_arity : int)
          (extra_args : list (Simple.t * Flambda_kind.With_subkind.t))
          (apply_cont_args :
            Continuation_callsite_map.t (Numeric_types.Int.Map.t T.Cont_arg.t)) =>
      Continuation.Map.update cont
        (fun (rewrite_map_opt :
               option
                 (Apply_cont_rewrite_id.Map.t
                    (Numeric_types.Int.Map.t T.Cont_arg.t))) =>
          let* rewrite_map :=
            Option.value rewrite_map_opt Apply_cont_rewrite_id.Map.empty
          in
          let* rewrite_map :=
            Apply_cont_rewrite_id.Map.update rewrite_id
              (fun x =>
                match x with
                | Some _ =>
                  fatal_errorf2 "Introducing a rewrite id twice %a"
                    Apply_cont_rewrite_id.print rewrite_id
                | None =>
                  let* map :=
                    let! tmp1 :=
                      List.init result_arity (fun i =>
                        ret (i, T.Cont_arg.Function_result))
                    in
                    Numeric_types.Int.Map.of_list tmp1
                  in
                  (* 262-263: the two arguments of the function are the
                     pairs [(i, map)] and [(extra_arg, _kind)]. *)
                  let* '(_, map) :=
                    List.fold_left
                      (fun pat pat' =>
                        let* '(i, map) := ret pat in
                        let* '(extra_arg, _kind) := ret pat' in
                        let* map :=
                          Numeric_types.Int.Map.add i
                            (T.Cont_arg.Simple extra_arg) map
                        in
                        ret (i + 1, map))
                      (1, map) extra_args
                  in
                  ret (Some map)
                end)
              rewrite_map
          in
          ret (Some rewrite_map))
        apply_cont_args
    in
    let* apply_cont_args :=
      let* '(rewrite_id, exn_cont) := ret exn_cont in
      let! tmp1 := Exn_continuation.extra_args exn_cont in
      let! tmp2 := Exn_continuation.exn_handler exn_cont in
      add_func_result tmp2 rewrite_id 1 tmp1
        elt.(Flow_types.Continuation_info.apply_cont_args)
    in
    let* apply_cont_args :=
      match result_cont with
      | None => ret apply_cont_args
      | Some (rewrite_id, result_cont) =>
        let! tmp1 := Flambda_arity.cardinal_unarized result_arity in
        add_func_result result_cont rewrite_id tmp1 [] apply_cont_args
      end
    in
    ret (update_apply_cont_args elt apply_cont_args)).

(* 295-331. In the compiler: [~rewrite_id cont arg_name_simples t]. *)
Definition add_apply_cont_args (rewrite_id : Apply_cont_rewrite_id.t)
    (cont : Continuation.t) (arg_name_simples : list Simple.t)
    (t : Flow_acc.t) : M Flow_acc.t :=
  update_top_of_stack t (fun elt =>
    let* apply_cont_args :=
      Continuation.Map.update cont
        (fun (rewrite_map_opt :
               option
                 (Apply_cont_rewrite_id.Map.t
                    (Numeric_types.Int.Map.t T.Cont_arg.t))) =>
          let* rewrite_map :=
            Option.value rewrite_map_opt Apply_cont_rewrite_id.Map.empty
          in
          let* rewrite_map :=
            Apply_cont_rewrite_id.Map.update rewrite_id
              (fun x =>
                match x with
                | Some _ =>
                  fatal_errorf2 "Introducing a rewrite id twice %a"
                    Apply_cont_rewrite_id.print rewrite_id
                | None =>
                  (* 316: the first argument of the function is the pair
                     [(map, i)]. *)
                  let* '(map, _) :=
                    List.fold_left
                      (fun pat arg_simple =>
                        let* '(map, i) := ret pat in
                        let* map :=
                          Numeric_types.Int.Map.add i
                            (T.Cont_arg.Simple arg_simple) map
                        in
                        ret (map, i + 1))
                      (Numeric_types.Int.Map.empty, 0)
                      arg_name_simples
                  in
                  ret (Some map)
                end)
              rewrite_map
          in
          ret (Some rewrite_map))
        elt.(Flow_types.Continuation_info.apply_cont_args)
    in
    ret (update_apply_cont_args elt apply_cont_args)).

(* 333-339. [Simple.pattern_match']: the arguments are in the order of the
   interface: [~var ~symbol ~const]. *)
Definition get_block_and_constant_field (block : Simple.t)
    (field : Target_ocaml_int.t) : M (option (Variable_.t * int)) :=
  Simple.pattern_match' block
    (fun var _ =>
      let* field := Target_ocaml_int.to_int field in
      ret (Some (var, field)))
    (fun _ _ => ret None)
    (fun _ => ret None).

(* 341-407 *)
Definition record_let_binding (rewrite_id : Named_rewrite_id.t)
    (generate_phantom_lets : bool) (let_bound : Bound_pattern.t)
    (simplified_defining_expr : Simplified_named.t) (t : Flow_acc.t)
    : M Flow_acc.t :=
  (* 343-344: [match simplified_defining_expr with { free_names; named;
     cost_metrics = _ } -> ...] *)
  let* '{| Simplified_named.free_names := free_names;
           Simplified_named.named := named;
           Simplified_named.cost_metrics := _
        |} :=
    ret simplified_defining_expr
  in
  let& record_var_bindings :=
    fun (t : Flow_acc.t) (free_names : Name_occurrences.t) =>
    Bound_pattern.fold_all_bound_vars let_bound t (fun t v =>
      let! tmp1 := Bound_var.var v in
      record_var_binding tmp1 free_names generate_phantom_lets t)
  in
  (* PORT-GAP(loose): 350 and 359, the attribute [@ocaml.warning "-4"] of the
     two matches is not kept. *)
  match named with
  | Simplified_named.Simple simple =>
    let* bound_var := Bound_pattern.must_be_singleton let_bound in
    let* var := Bound_var.var bound_var in
    record_var_alias var simple t
  | Simplified_named.Set_of_closures _ _ | Simplified_named.Rec_info _ =>
    record_var_bindings t free_names
  | Simplified_named.Prim original_prim _ =>
    let* bound_var := Bound_pattern.must_be_singleton let_bound in
    let* var := Bound_var.var bound_var in
    match original_prim with
    | Flambda_primitive.Unary (Flambda_primitive.End_region _) _region =>
      (* Uses of region variables in [End_region] don't count as uses. *)
      ret t
    | Flambda_primitive.Unary (Flambda_primitive.Is_int _) simple =>
      let! tmp1 := Simple.must_be_var simple in
      match tmp1 with
      | Some (v, _) =>
        let! tmp2 :=
          record_ref_named rewrite_id var original_prim
            (T.Mutable_prim.Is_int v) t
        in
        record_var_bindings tmp2 Name_occurrences.empty
      | None => record_var_bindings t free_names
      end
    | Flambda_primitive.Unary Flambda_primitive.Get_tag simple =>
      let! tmp1 := Simple.must_be_var simple in
      match tmp1 with
      | Some (v, _) =>
        let! tmp2 :=
          record_ref_named rewrite_id var original_prim
            (T.Mutable_prim.Get_tag v) t
        in
        record_var_bindings tmp2 Name_occurrences.empty
      | None => record_var_bindings t free_names
      end
    | Flambda_primitive.Unary (Flambda_primitive.Block_load bak mut field)
        block =>
      let! tmp1 := get_block_and_constant_field block field in
      match tmp1 with
      | Some (block, field) =>
        let! tmp2 :=
          record_ref_named rewrite_id var original_prim
            (T.Mutable_prim.Block_load bak mut block field)
            t
        in
        record_var_bindings tmp2 Name_occurrences.empty
      | None => record_var_bindings t free_names
      end
    | Flambda_primitive.Binary (Flambda_primitive.Block_set bak _ field) block
        value =>
      let! tmp1 := get_block_and_constant_field block field in
      match tmp1 with
      | Some (block, field) =>
        record_ref_named rewrite_id var original_prim
          (T.Mutable_prim.Block_set bak block field value)
          t
      | None => add_used_in_current_handler free_names t
      end
    | Flambda_primitive.Variadic
        (Flambda_primitive.Make_block kind mut alloc_mode) fields =>
      let! tmp1 :=
        record_ref_named rewrite_id var original_prim
          (T.Mutable_prim.Make_block kind mut alloc_mode fields)
          t
      in
      record_var_bindings tmp1 Name_occurrences.empty
    | _ =>
      let! tmp1 := Flambda_primitive.at_most_generative_effects original_prim in
      if tmp1
      then (* the primitive can be removed *)
        record_var_bindings t free_names
      else
        let* t := record_defined_var var t in
        add_used_in_current_handler free_names t
    end
  end.

(* Lifted symbols *)

(* 411-417. In the compiler: [~free_names ~value_slots _ (symbol, _) elt]. *)
Definition record_lifted_function_slot_aux {A B : Type}
    (free_names : Name_occurrences.t) (value_slots : Value_slot.Map.t Simple.t)
    (_ : A) (pat : Symbol.t * B) (elt : cont_info) : M cont_info :=
  let* '(symbol, _) := ret pat in
  let* elt := record_symbol_binding_aux symbol free_names elt in
  Value_slot.Map.fold
    (fun value_slot simple elt =>
      let! tmp1 := Simple.free_names simple in
      let! tmp2 := Name.symbol symbol in
      record_value_slot_aux tmp2 value_slot tmp1 elt)
    value_slots elt.

(* 419-452. In the compiler: [~being_defined elt definition]. *)
Definition record_lifted_constant_definition_aux
    (being_defined : Name_occurrences.t) (elt : cont_info)
    (definition : Lifted_constant.Definition_.t) : M cont_info :=
  (* PORT-GAP(loose): 420, the local module [D = Lifted_constant.Definition]
     is written out. *)
  let! tmp1 := Lifted_constant.Definition_.descr definition in
  match tmp1 with
  | Lifted_constant.Definition_.Code code_id =>
    let! tmp2 := Lifted_constant.Definition_.free_names definition in
    let! tmp3 := Name_occurrences.union being_defined tmp2 in
    record_code_id_binding_aux code_id tmp3 elt
  | Lifted_constant.Definition_.Block_like symbol _ _ _ =>
    let* free_names :=
      let! tmp2 := Lifted_constant.Definition_.free_names definition in
      Name_occurrences.union being_defined tmp2
    in
    record_symbol_binding_aux symbol free_names elt
  | Lifted_constant.Definition_.Set_of_closures _ closure_symbols_with_types
      _ =>
    let* expr := Lifted_constant.Definition_.defining_expr definition in
    let! tmp2 := Rebuilt_static_const.to_const expr in
    match tmp2 with
    | Some (Flambda.Static_const const) =>
      let* set_of_closures := Static_const.must_be_set_of_closures const in
      let* free_names :=
        let! tmp3 := Set_of_closures.function_decls set_of_closures in
        let! tmp4 := Function_declarations.free_names tmp3 in
        Name_occurrences.union being_defined tmp4
      in
      let* value_slots := Set_of_closures.value_slots set_of_closures in
      Function_slot.Lmap.fold
        (record_lifted_function_slot_aux free_names value_slots)
        closure_symbols_with_types elt
    | None | Some (Flambda.Code _) | Some Flambda.Deleted_code =>
      let* free_names :=
        let! tmp3 := Lifted_constant.Definition_.free_names definition in
        Name_occurrences.union being_defined tmp3
      in
      (* 450: the second argument of the function is the pair
         [(symbol, _)]. *)
      Function_slot.Lmap.fold
        (fun _ pat elt =>
          let* '(symbol, _) := ret pat in
          record_symbol_binding_aux symbol free_names elt)
        closure_symbols_with_types elt
    end
  end.

(* 454-481 *)
Definition normalize_lifted_constant_aux (lifted_constant : Lifted_constant.t)
    (elt : cont_info) : M cont_info :=
  let* being_defined :=
    let* bound_static := Lifted_constant.bound_static lifted_constant in
    (* Note: We're not registering code IDs in the set, because we can actually
       delete code bindings individually. In particular, code IDs that are only
       used in the newer_version_of field of another binding will be deleted as
       expected. *)
    let* symbols := Bound_static.symbols_being_defined bound_static in
    (* 462-466: [a |> f b c] is [f b c a] *)
    Symbol.Set_.fold
      (fun symbol acc =>
        Name_occurrences.add_symbol acc symbol Name_mode.normal)
      symbols Name_occurrences.empty
  in
  (* Record all projections as potential dependencies. *)
  let* elt :=
    let! tmp1 := Lifted_constant.symbol_projections lifted_constant in
    Variable_.Map.fold
      (fun var proj elt =>
        let! tmp2 := Symbol_projection.free_names proj in
        record_symbol_projection_aux var tmp2 elt)
      tmp1 elt
  in
  (* 476-480: [ListLabels.fold_left ~init (..) ~f]: the arguments are in the
     order of the interface. *)
  let* elt :=
    let! tmp1 := Lifted_constant.definitions lifted_constant in
    ListLabels.fold_left
      (record_lifted_constant_definition_aux being_defined)
      elt tmp1
  in
  ret elt.

(* 483-486 *)
Definition normalize_lifted_constants_aux
    (lifted_constants : Lifted_constant_state.t) (elt : cont_info)
    : M cont_info :=
  Lifted_constant_state.fold lifted_constants elt
    (fun elt lifted_constant =>
      normalize_lifted_constant_aux lifted_constant elt).

(* PORT-GAP(update): 489-492, [{ t with lifted_constants }]. *)
Definition update_lifted_constants (t : T.Acc.t)
    (lifted_constants : Lifted_constant_state.t) : T.Acc.t :=
  {| T.Acc.stack := t.(Flow_types.Acc.stack);
     T.Acc.map := t.(Flow_types.Acc.map);
     T.Acc.extra := t.(Flow_types.Acc.extra);
     T.Acc.lifted_constants := lifted_constants;
     T.Acc.dummy_toplevel_cont := t.(Flow_types.Acc.dummy_toplevel_cont)
  |}.
Extract Inlined Constant update_lifted_constants =>
  "(fun t lifted_constants -> { t with T.Acc.lifted_constants =
   lifted_constants })".

(* 488-492 *)
Definition record_lifted_constants (lifted_constants : Lifted_constant_state.t)
    (t : Flow_acc.t) : M Flow_acc.t :=
  let! tmp1 :=
    Lifted_constant_state.union lifted_constants
      t.(Flow_types.Acc.lifted_constants)
  in
  ret (update_lifted_constants t tmp1).

(* Normalisation *)
(* ************* *)

(* 497-525. In the compiler: [~extra_args rewrite_id original_args]. *)
Definition add_extra_args_to_call
    (extra_args :
      Apply_cont_rewrite_id.Map.t (Or_invalid.t (list EPA.Extra_arg.t)))
    (rewrite_id : Apply_cont_rewrite_id.t)
    (original_args : Numeric_types.Int.Map.t T.Cont_arg.t)
    : M (option (Numeric_types.Int.Map.t T.Cont_arg.t)) :=
  let! tmp1 := Apply_cont_rewrite_id.Map.find_or_null rewrite_id extra_args in
  match tmp1 with
  | Or_null.Null => ret (Some original_args)
  | Or_null.This Or_invalid.Invalid => ret None
  | Or_null.This (Or_invalid.Ok extra_args) =>
    let* args_acc :=
      let! tmp2 := Numeric_types.Int.Map.is_empty original_args in
      if tmp2
      then ret (0, Numeric_types.Int.Map.empty)
      else
        let* '(max_arg, _) := Numeric_types.Int.Map.max_binding original_args in
        ret (max_arg + 1, original_args)
    in
    let* extra_args :=
      List.map
        (fun x =>
          match x with
          | EPA.Extra_arg.Already_in_scope s => ret (T.Cont_arg.Simple s)
          | EPA.Extra_arg.New_let_binding v prim =>
            let! tmp2 := Flambda_primitive.free_names prim in
            ret (T.Cont_arg.New_let_binding v tmp2)
          | EPA.Extra_arg.New_let_binding_with_named_args v _ =>
            ret (T.Cont_arg.New_let_binding v Name_occurrences.empty)
          end)
        extra_args
    in
    (* 521: the first argument of the function is the pair [(i, args)]. *)
    let* '(_, args) :=
      List.fold_left
        (fun pat extra_arg =>
          let* '(i, args) := ret pat in
          let! tmp2 := Numeric_types.Int.Map.add i extra_arg args in
          ret (i + 1, tmp2))
        args_acc extra_args
    in
    ret (Some args)
  end.

(* PORT-GAP(update): 623, [{ elt with params }]. *)
Definition update_params (t : T.Continuation_info.t)
    (params : Bound_parameters.t) : T.Continuation_info.t :=
  {| T.Continuation_info.continuation :=
       t.(Flow_types.Continuation_info.continuation);
     T.Continuation_info.recursive :=
       t.(Flow_types.Continuation_info.recursive);
     T.Continuation_info.is_exn_handler :=
       t.(Flow_types.Continuation_info.is_exn_handler);
     T.Continuation_info.params := params;
     T.Continuation_info.parent_continuation :=
       t.(Flow_types.Continuation_info.parent_continuation);
     T.Continuation_info.used_in_handler :=
       t.(Flow_types.Continuation_info.used_in_handler);
     T.Continuation_info.bindings := t.(Flow_types.Continuation_info.bindings);
     T.Continuation_info.direct_aliases :=
       t.(Flow_types.Continuation_info.direct_aliases);
     T.Continuation_info.mutable_let_prims_rev :=
       t.(Flow_types.Continuation_info.mutable_let_prims_rev);
     T.Continuation_info.defined := t.(Flow_types.Continuation_info.defined);
     T.Continuation_info.code_ids := t.(Flow_types.Continuation_info.code_ids);
     T.Continuation_info.value_slots :=
       t.(Flow_types.Continuation_info.value_slots);
     T.Continuation_info.apply_cont_args :=
       t.(Flow_types.Continuation_info.apply_cont_args)
  |}.
Extract Inlined Constant update_params =>
  "(fun t params -> { t with T.Continuation_info.params = params })".

(* PORT-GAP(update): 638, [{ t with map; extra }]. *)
Definition update_map_extra (t : T.Acc.t)
    (map : Continuation.Map.t T.Continuation_info.t)
    (extra : Continuation.Map.t Continuation_extra_params_and_args.t)
    : T.Acc.t :=
  {| T.Acc.stack := t.(Flow_types.Acc.stack);
     T.Acc.map := map;
     T.Acc.extra := extra;
     T.Acc.lifted_constants := t.(Flow_types.Acc.lifted_constants);
     T.Acc.dummy_toplevel_cont := t.(Flow_types.Acc.dummy_toplevel_cont)
  |}.
Extract Inlined Constant update_map_extra =>
  "(fun t map extra -> { t with T.Acc.map = map; extra = extra })".

(* 527-638 *)
Definition normalize_acc
    (specialization_map :
      Continuation.Map.t (Apply_cont_rewrite_id.Map.t Continuation.t))
    (t : T.Acc.t) : M T.Acc.t :=
  (* 528-579 *)
  let* map :=
    Continuation.Map.map
      (fun (elt : T.Continuation_info.t) =>
        (* Note: [cont=elt.continuation] *)
        (* Rewrite continuations calls to the specialized ones *)
        let* apply_cont_args :=
          Continuation.Map.fold
            (fun cont rewrite_ids acc =>
              let! tmp1 :=
                Continuation.Map.find_or_null cont specialization_map
              in
              match tmp1 with
              | Or_null.Null => Continuation.Map.add cont rewrite_ids acc
              | Or_null.This specialized_ids =>
                Apply_cont_rewrite_id.Map.fold
                  (fun id args acc =>
                    let! tmp2 :=
                      Apply_cont_rewrite_id.Map.find_or_null id specialized_ids
                    in
                    match tmp2 with
                    | Or_null.Null =>
                      Continuation_callsite_map.add cont id args acc
                    | Or_null.This specialized =>
                      Continuation_callsite_map.add specialized id args acc
                    end)
                  rewrite_ids acc
              end)
            elt.(Flow_types.Continuation_info.apply_cont_args)
            Continuation.Map.empty
        in
        (* Add extra args to the continuation call sites *)
        let* apply_cont_args :=
          Continuation.Map.filter_map
            (fun cont rewrite_ids =>
              let* rewrite_ids :=
                let! tmp1 :=
                  Continuation.Map.find_or_null cont t.(Flow_types.Acc.extra)
                in
                match tmp1 with
                | Or_null.Null => ret rewrite_ids
                | Or_null.This epa =>
                  let* extra_args := EPA.extra_args epa in
                  Apply_cont_rewrite_id.Map.filter_map
                    (add_extra_args_to_call extra_args)
                    rewrite_ids
                end
              in
              (* We must not leave an empty [Apply_cont_rewrite_id] map here.
                 Indeed, not having any actual continuation arguments will let
                 flow analysis find a dominator for parameters of [cont] that we
                 do not have access to. Since we then only look at which
                 continuation can call which to know which arguments to add,
                 this causes the adding of the extra parameters to assume we
                 need access to that dominator since it looks like we can call
                 [cont], but since neither we nor any of our callers have access
                 to it, trying to add the dominator crashes the compiler. *)
              let! tmp1 := Apply_cont_rewrite_id.Map.is_empty rewrite_ids in
              if tmp1 then ret None else ret (Some rewrite_ids))
            apply_cont_args
        in
        ret (update_apply_cont_args elt apply_cont_args))
      t.(Flow_types.Acc.map)
  in
  (* 580-614 *)
  let* map :=
    Continuation.Map.map
      (fun (elt : T.Continuation_info.t) =>
        let* defined :=
          Continuation.Map.fold
            (fun callee_cont rewrite_ids defined =>
              let! tmp1 :=
                Continuation.Map.find_or_null callee_cont
                  t.(Flow_types.Acc.extra)
              in
              match tmp1 with
              | Or_null.Null => ret defined
              | Or_null.This epa =>
                Apply_cont_rewrite_id.Map.fold
                  (fun rewrite_id _args defined =>
                    let! tmp2 := EPA.extra_args epa in
                    let! tmp3 :=
                      Apply_cont_rewrite_id.Map.find_or_null rewrite_id tmp2
                    in
                    match tmp3 with
                    | Or_null.Null => ret defined
                    | Or_null.This Or_invalid.Invalid => ret defined
                    | Or_null.This (Or_invalid.Ok extra_args) =>
                      let* defined :=
                        List.fold_left
                          (fun defined x =>
                            match x with
                            | EPA.Extra_arg.Already_in_scope _ => ret defined
                            | EPA.Extra_arg.New_let_binding v _
                            | EPA.Extra_arg.New_let_binding_with_named_args v
                                _ =>
                              Variable_.Set_.add v defined
                            end)
                          defined extra_args
                      in
                      ret defined
                    end)
                  rewrite_ids defined
              end)
            elt.(Flow_types.Continuation_info.apply_cont_args)
            elt.(Flow_types.Continuation_info.defined)
        in
        ret (update_defined elt defined))
      map
  in
  (* 615-627 *)
  let* map :=
    Continuation.Map.fold
      (fun cont epa map =>
        let* elt := Continuation.Map.find cont map in
        let* elt :=
          let* params :=
            let! tmp1 := EPA.extra_params epa in
            Bound_parameters.append
              elt.(Flow_types.Continuation_info.params) tmp1
          in
          ret (update_params elt params)
        in
        Continuation.Map.add cont elt map)
      t.(Flow_types.Acc.extra) map
  in
  (* 628-637 *)
  let* map :=
    Continuation.Map.update t.(Flow_types.Acc.dummy_toplevel_cont)
      (fun x =>
        match x with
        | None =>
          fatal_errorf0
            "Data_flow: missing continuation info for top-level expression"
        | Some elt =>
          let! tmp1 :=
            normalize_lifted_constants_aux
              t.(Flow_types.Acc.lifted_constants) elt
          in
          ret (Some tmp1)
        end)
      map
  in
  ret (update_map_extra t map Continuation.Map.empty).
