(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/original_handlers.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN], the arguments by place) is that of GUIDE.md; the Rocq
   form of the type [t] is that of decl/Original_handlers.v. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation Flambda Format
  Lifted_cont_params Non_recursive_handler One_recursive_handler.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16-23 *)
(* PORT-GAP(type): the type has an inline record: the OCaml definition is
   the compiler's text; in Rocq, the form of decl/Original_handlers.v (the
   fields of [Recursive] by place). *)
(*OCAML
type t =
  | Recursive of
      { invariant_params : Bound_parameters.t;
        lifted_params : Lifted_cont_params.t;
        continuation_handlers : One_recursive_handler.t Continuation.Lmap.t;
        can_be_lifted : bool
      }
  | Non_recursive of Non_recursive_handler.t
OCAML*)
Inductive t : Type :=
| Recursive :
    Bound_parameters.t -> Lifted_cont_params.t ->
    Continuation.Lmap.t One_recursive_handler.t -> bool -> t
| Non_recursive : Non_recursive_handler.t -> t.
Extract Inductive t => "t"
  [ "(fun (x__1, x__2, x__3, x__4) -> Recursive { invariant_params = x__1; lifted_params = x__2; continuation_handlers = x__3; can_be_lifted = x__4 })"
    "Non_recursive" ]
  "(fun f__1 f__2 x__0 -> match x__0 with Recursive { invariant_params = x__1; lifted_params = x__2; continuation_handlers = x__3; can_be_lifted = x__4 } -> f__1 x__1 x__2 x__3 x__4 | Non_recursive x__1 -> f__2 x__1)".

(* 25-40 *)
(* PORT-GAP(loose): 25, the attribute [@ocamlformat "disable"] is not kept.
   30-31: the compiler's string has a new line and eight spaces after its
   first parenthesis (the line does not end with a backslash). *)
Definition print (ppf : Format.formatter) (t : Original_handlers.t)
    : M unit :=
  match t with
  | Non_recursive non_rec_handler =>
    Non_recursive_handler.print ppf non_rec_handler
  | Recursive invariant_params lifted_params continuation_handlers
      can_be_lifted =>
    (* 39 *)
    let! tmp1 := papp1 Continuation.Lmap.print One_recursive_handler.print in
    Format.fprintf7 ppf
      "@[<hov 1>(
        @[<hv 1>(can_be_lifted@ %b)@]@ @[<hv 1>(invariant params@ %a)@]@ @[<hv 1>(lifted_params@ %a)@]@ @[<hv 1>(continuation handlers@ %a)@])@]"
      can_be_lifted Bound_parameters.print invariant_params
      Lifted_cont_params.print lifted_params tmp1 continuation_handlers
  end.

(* 42-45 *)
Definition create_recursive (invariant_params : Bound_parameters.t)
    (lifted_params : Lifted_cont_params.t)
    (continuation_handlers : Continuation.Lmap.t One_recursive_handler.t)
    (can_be_lifted : bool) : M t :=
  ret
    (Recursive invariant_params lifted_params continuation_handlers
       can_be_lifted).

(* 47 *)
Definition create_non_recursive (non_rec_handler : Non_recursive_handler.t)
    : M t :=
  ret (Non_recursive non_rec_handler).

(* 49-52 *)
Definition bound_continuations (t : Original_handlers.t)
    : M (list Continuation.t) :=
  match t with
  | Non_recursive non_rec_handler =>
    ret [non_rec_handler.(Non_recursive_handler.cont)]
  | Recursive _ _ continuation_handlers _ =>
    Continuation.Lmap.keys continuation_handlers
  end.

(* 54-56 *)
Definition can_be_lifted (t : Original_handlers.t) : M bool :=
  match t with
  | Non_recursive
      {| Non_recursive_handler.can_be_lifted := can_be_lifted |} =>
    ret can_be_lifted
  | Recursive _ _ _ can_be_lifted => ret can_be_lifted
  end.

(* 58-97 *)
Definition add_params_to_lift (t : Original_handlers.t)
    (params_to_lift : Lifted_cont_params.t) : M Original_handlers.t :=
  let* '(lifted_params, renaming) := Lifted_cont_params.rename params_to_lift in
  (* PORT-GAP(loose): 60, the attribute [@inline] is not kept. *)
  let& fail :=
    fun (_ : unit) =>
    (fatal_errorf4
       "Cannot add lifted params to a continuation that already has lifted params:@ params_to_lift=%a@ t=%a"
       Lifted_cont_params.print params_to_lift print t
     : M Original_handlers.t)
  in
  match t with
  (* 67-68: [Recursive ({ lifted_params = old_lifted; continuation_handlers;
     _ } as recursive)]; the fields are by place, and 78, [{ recursive with
     lifted_params; continuation_handlers }], names all of them. *)
  | Recursive invariant_params old_lifted continuation_handlers
      can_be_lifted =>
    let! tmp1 := Lifted_cont_params.is_empty old_lifted in
    if tmp1
    then
      let* continuation_handlers :=
        Continuation.Lmap.map
          (fun '({| One_recursive_handler.params := params;
                    One_recursive_handler.handler := handler;
                    One_recursive_handler.is_cold := is_cold
                 |} : One_recursive_handler.t) =>
            let* handler := Flambda.Expr.apply_renaming handler renaming in
            One_recursive_handler.create params handler is_cold)
          continuation_handlers
      in
      ret
        (Recursive invariant_params lifted_params continuation_handlers
           can_be_lifted)
    else fail tt
  | Non_recursive
      {| Non_recursive_handler.cont := cont;
         Non_recursive_handler.params := params;
         Non_recursive_handler.lifted_params := old_lifted;
         Non_recursive_handler.handler := handler;
         Non_recursive_handler.is_exn_handler := is_exn_handler;
         Non_recursive_handler.can_be_lifted := can_be_lifted;
         Non_recursive_handler.is_cold := is_cold
      |} =>
    let! tmp1 := Lifted_cont_params.is_empty old_lifted in
    if tmp1
    then
      let* handler := Flambda.Expr.apply_renaming handler renaming in
      let* non_rec :=
        Non_recursive_handler.create cont params lifted_params handler
          is_exn_handler can_be_lifted is_cold
      in
      ret (Non_recursive non_rec)
    else fail tt
  end.
