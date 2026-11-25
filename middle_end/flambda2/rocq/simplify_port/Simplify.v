(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function under the
   compiler's names; the numbers in the comments are the lines of that file.
   What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Code_id Continuation_uses_env Exported_code
  Flambda_arity Flambda_cmx Flambda_features Name Name_occurrences Or_unknown
  Simplify_expr Slot_offsets Target_system Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Or_unknown.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* PORT-GAP(verbatim): 19-25, the compiler's definition of the type, as it
   is. *)
(*OCAML
type simplify_result =
  { free_names : Name_occurrences.t;
    final_typing_env : Typing_env.t;
    all_code : Exported_code.t;
    slot_offsets : Slot_offsets.t;
    unit : Flambda_unit.t
  }
OCAML*)

(* PORT-GAP(type): 19-25, a plain record, but Rocq's extraction does not
   keep a field of the name [unit] (it prints [coq_unit]). So the type is
   abstract here, in the form of decl/, with a maker that takes the fields
   by place in the order of the type. *)
Parameter simplify_result : Type.
Extract Inlined Constant simplify_result => "simplify_result".
Parameter mk_simplify_result :
  Name_occurrences.t -> TE.t -> Exported_code.t -> Slot_offsets.t ->
  Flambda_unit.t -> simplify_result.
Extract Inlined Constant mk_simplify_result => "(fun x__1 x__2 x__3 x__4 x__5 -> { free_names = x__1; final_typing_env = x__2; all_code = x__3; slot_offsets = x__4; unit = x__5 })".

(* 27-99. In the compiler: [~cmx_loader ~machine_width ~round
   ~code_slot_offsets unit]. *)
Definition run (cmx_loader : Flambda_cmx.loader)
    (machine_width : Target_system.Machine_width.t) (round : int)
    (code_slot_offsets : Code_id.Map.t Slot_offsets.t) (unit : Flambda_unit.t)
    : M simplify_result :=
  let* return_continuation := FU.return_continuation unit in
  let* exn_continuation := FU.exn_continuation unit in
  let* toplevel_my_alloc_region := FU.toplevel_my_alloc_region unit in
  let* module_symbol := FU.module_symbol unit in
  (* 32-33 *)
  let* resolver := papp1 Flambda_cmx.load_cmx_file_contents cmx_loader in
  let* get_imported_code := papp1 Flambda_cmx.get_imported_code cmx_loader in
  (* 34-39: the arguments are in the order of the interface (the exception
     continuation before the return continuation). *)
  let* denv :=
    let! tmp1 := Flambda_features.float_const_prop tt in
    DE.create round machine_width resolver get_imported_code tmp1
      exn_continuation return_continuation toplevel_my_alloc_region
  in
  (* 42 *)
  let* dacc := DA.create denv code_slot_offsets Continuation_uses_env.empty in
  (* 43-47 *)
  let* '(body, uacc) :=
    let! tmp1 := Flambda_arity.create_singletons [K.With_subkind.any_value] in
    let! tmp2 := FU.body unit in
    Simplify_expr.simplify_toplevel dacc tmp2 return_continuation tmp1
      exn_continuation
  in
  let* body :=
    let! tmp1 := UA.are_rebuilding_terms uacc in
    Rebuilt_expr.to_expr body tmp1
  in
  let* name_occurrences := UA.name_occurrences uacc in
  (* 50-59 *)
  NO.fold_names name_occurrences tt
    (* The parameter [unit] hides Rocq's type of that name. *)
    (fun (_ : Datatypes.unit) name =>
      Name.pattern_match name
        (fun var =>
          let! tmp1 := Variable_.equal var toplevel_my_alloc_region in
          if negb tmp1
          then
            fatal_errorf4
              "Variable %a not expected to be free in whole-compilation-unit term:@ %a"
              Variable_.print var Expr.print body
          else ret tt)
        (fun _symbol => ret tt)) ;;
  (* 60-63 *)
  (let! tmp1 := UA.lifted_constants uacc in
   let! tmp2 := LCS.is_empty tmp1 in
   if negb tmp2
   then
     fatal_errorf2 "Lifted constants accumulator should be empty:@ %a" UA.print
       uacc
   else ret tt) ;;
  (* 64-76 *)
  let* final_typing_env :=
    let* cont_uses_env :=
      let! tmp1 := UA.creation_dacc uacc in
      DA.continuation_uses_env tmp1
    in
    let! tmp1 :=
      Continuation_uses_env.get_typing_env_no_more_than_one_use cont_uses_env
        return_continuation
    in
    match tmp1 with
    | Some final_typing_env => ret final_typing_env
    | None =>
      (* Create an unknown typing_env in case the module never returns *)
      let! tmp1 := TE.create machine_width resolver in
      TE.add_symbol_definition tmp1 module_symbol
    end
  in
  (* The end of the unit is where the return continuation is called. *)
  TE.notify_test_observer final_typing_env return_continuation ;;
  (* 79-82 *)
  let* all_code :=
    let! tmp1 := get_imported_code tt in
    let! tmp2 := Exported_code.mark_as_imported tmp1 in
    let! tmp3 := UA.all_code uacc in
    Exported_code.merge tmp3 tmp2
  in
  let* name_occurrences := UA.name_occurrences uacc in
  (* 84-89 *)
  let* slot_offsets :=
    let! tmp1 := UA.slot_offsets uacc in
    match tmp1 with
    | Or_unknown.Unknown =>
      fatal_error "Slot offsets must be computed and cannot be unknown"
    | Or_unknown.Known slot_offsets => ret slot_offsets
    end
  in
  (* 90-93: the arguments are in the order of the interface. *)
  let* unit :=
    FU.create return_continuation exn_continuation toplevel_my_alloc_region
      body module_symbol
  in
  (* 94-99: the fields by place, in the order of the type. *)
  ret
    (mk_simplify_result name_occurrences final_typing_env all_code
       slot_offsets unit).
