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

(* This file follows
   middle_end/flambda2/simplify/env/continuation_uses_env.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition under
   the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order, the arguments by place) is that of GUIDE.md. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameters
  Continuation Continuation_use_kind Continuation_uses Downwards_env
  Flambda2_types Flambda_arity Format Misc Non_recursive_handler
  One_continuation_use One_recursive_handler Option Or_bottom Or_null
  Original_handlers.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* PORT-GAP(verbatim): 17-18, the two abbreviations of modules are the
   compiler's text, and the Rocq text below writes the modules' own names.
   As Rocq modules ([Module T := Flambda2_types.]) they make Rocq write
   [open Flambda2_types] and [open Tag] in the extracted file, and after
   them OCaml reads the type [Map.t] of the record's fields, which Rocq
   prints after [open Continuation], as [Tag.Map.t]. *)
(*OCAML
module DE = Downwards_env
module T = Flambda2_types
OCAML*)

(* 20-23 *)
Record t : Type :=
  { continuation_uses : Continuation.Map.t Continuation_uses.t;
    continuation_arities : Continuation.Map.t Flambda_arity.t_Unarized
  }.

(* 25-31 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept, and
   the record pattern of the parameter is a match. *)
Definition print (ppf : Format.formatter) (t : Continuation_uses_env.t)
    : M unit :=
  match t with
  | {| continuation_uses := continuation_uses;
       continuation_arities := continuation_arities
    |} =>
    (* PORT-GAP(papp): [Continuation.Map.print] is given its first argument
       only, twice. *)
    let! tmp1 := papp1 Continuation.Map.print Flambda_arity.print in
    let! tmp2 := papp1 Continuation.Map.print Continuation_uses.print in
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(continuation_uses@ %a)@]@ @[<hov 1>(continuation_arities@ %a)@])@]"
      tmp2 continuation_uses tmp1 continuation_arities
  end.

(* 33-36 *)
Definition empty : t :=
  {| continuation_uses := Continuation.Map.empty;
     continuation_arities := Continuation.Map.empty
  |}.

(* PORT-GAP(update): 50, [{ t with continuation_arities }]. *)
Definition update_continuation_arities (t : Continuation_uses_env.t)
    (continuation_arities : Continuation.Map.t Flambda_arity.t_Unarized)
    : Continuation_uses_env.t :=
  {| continuation_uses := t.(continuation_uses);
     continuation_arities := continuation_arities
  |}.
Extract Inlined Constant update_continuation_arities =>
  "(fun t x__1 -> { t with continuation_arities = x__1 })".

(* 38-50 *)
Definition record_continuation (t : Continuation_uses_env.t)
    (cont : Continuation.t) (arity : Flambda_arity.t_Unarized)
    : M Continuation_uses_env.t :=
  let* continuation_arities :=
    Continuation.Map.update cont
      (fun o =>
        match o with
        | Some _ =>
          fatal_errorf2
            "[CUE.record_continuation]: continuation %a already present in continuation_uses_env"
            Continuation.print cont
        | None => ret (Some arity)
        end)
      t.(continuation_arities)
  in
  ret (update_continuation_arities t continuation_arities).

(* 52-63 *)
Definition record_continuation_arity (t : Continuation_uses_env.t)
    (handlers : Original_handlers.t) : M Continuation_uses_env.t :=
  match handlers with
  | Original_handlers.Non_recursive
      {| Non_recursive_handler.cont := cont;
         Non_recursive_handler.params := params
      |} =>
    let! tmp1 := Bound_parameters.arity params in
    record_continuation t cont tmp1
  | Original_handlers.Recursive invariant_params _ continuation_handlers _ =>
    let* invariant_arity := Bound_parameters.arity invariant_params in
    Continuation.Lmap.fold
      (fun cont (handler : One_recursive_handler.t) cont_uses_env =>
        let! tmp1 :=
          Bound_parameters.arity handler.(One_recursive_handler.params)
        in
        let! tmp2 := Flambda_arity.concat invariant_arity tmp1 in
        record_continuation cont_uses_env cont tmp2)
      continuation_handlers t
  end.

(* PORT-GAP(update): 104, [{ t with continuation_uses }]. *)
Definition update_continuation_uses (t : Continuation_uses_env.t)
    (continuation_uses : Continuation.Map.t Continuation_uses.t)
    : Continuation_uses_env.t :=
  {| continuation_uses := continuation_uses;
     continuation_arities := t.(continuation_arities)
  |}.
Extract Inlined Constant update_continuation_uses =>
  "(fun t x__1 -> { t with continuation_uses = x__1 })".

(* 65-104 *)
Definition add_continuation_use (t : Continuation_uses_env.t)
    (cont : Continuation.t) (kind : Continuation_use_kind.t)
    (id : Apply_cont_rewrite_id.t) (env_at_use : Downwards_env.t)
    (arg_types : list Flambda2_types.t) : M Continuation_uses_env.t :=
  let* arity :=
    let! tmp1 := Continuation.Map.find_opt cont t.(continuation_arities) in
    match tmp1 with
    | None =>
      fatal_errorf4
        "[CUE.add_continuation_use]: Continuation %a not found in continuation_uses_env %a"
        Continuation.print cont print t
    | Some arity => ret arity
    end
  in
  let* '(arg_types, env_at_use) :=
    (* Refine types based on arity of continuation *)
    let* tenv := Downwards_env.typing_env env_at_use in
    let* machine_width := Flambda2_types.Typing_env.machine_width tenv in
    let* '(tenv, arg_types) :=
      let! tmp1 := Flambda_arity.unarized_components arity in
      Misc.Stdlib.List.fold_left_map2
        (fun tenv arg_type kind =>
          let* kind_ty :=
            Flambda2_types.unknown_with_subkind None machine_width kind
          in
          let! tmp2 := Flambda2_types.meet tenv arg_type kind_ty in
          match tmp2 with
          | Or_bottom.Bottom => ret (tenv, arg_type)
          | Or_bottom.Ok (arg_type, env) => ret (env, arg_type)
          end)
        tenv arg_types tmp1
    in
    let! tmp1 := Downwards_env.with_typing_env env_at_use tenv in
    ret (arg_types, tmp1)
  in
  let* use := One_continuation_use.create kind env_at_use id arg_types in
  let* continuation_uses :=
    Continuation.Map.update cont
      (fun o =>
        match o with
        | None =>
          let* uses := Continuation_uses.create cont arity in
          let! tmp1 := Continuation_uses.add_use uses use in
          ret (Some tmp1)
        | Some uses =>
          let! tmp1 := Continuation_uses.add_use uses use in
          ret (Some tmp1)
        end)
      t.(continuation_uses)
  in
  ret (update_continuation_uses t continuation_uses).

(* 106-109 *)
Definition record_continuation_use (t : Continuation_uses_env.t)
    (cont : Continuation.t) (kind : Continuation_use_kind.t)
    (env_at_use : Downwards_env.t) (arg_types : list Flambda2_types.t)
    : M (Continuation_uses_env.t * Apply_cont_rewrite_id.t) :=
  let* id := Apply_cont_rewrite_id.create tt in
  let* t := add_continuation_use t cont kind id env_at_use arg_types in
  ret (t, id).

(* 111-115 *)
Definition get_typing_env_no_more_than_one_use (t : Continuation_uses_env.t)
    (k : Continuation.t) : M (option Flambda2_types.Typing_env.t) :=
  let! tmp1 := Continuation.Map.find_or_null k t.(continuation_uses) in
  match tmp1 with
  | Or_null.Null => ret None
  | Or_null.This cont_uses =>
    Continuation_uses.get_typing_env_no_more_than_one_use cont_uses
  end.

(* 117-118 *)
Definition get_continuation_uses (t : Continuation_uses_env.t)
    (cont : Continuation.t) : M (option Continuation_uses.t) :=
  Continuation.Map.find_opt cont t.(continuation_uses).

(* 120-123 *)
Definition num_continuation_uses (t : Continuation_uses_env.t)
    (cont : Continuation.t) : M int :=
  let! tmp1 := Continuation.Map.find_or_null cont t.(continuation_uses) in
  match tmp1 with
  | Or_null.Null => ret 0
  | Or_null.This uses => Continuation_uses.number_of_uses uses
  end.

(* 125 *)
Definition all_continuations_used (t : Continuation_uses_env.t)
    : M Continuation.Set_.t :=
  Continuation.Map.keys t.(continuation_uses).

(* 127-143 *)
Definition union (t1 t2 : Continuation_uses_env.t)
    : M Continuation_uses_env.t :=
  let* continuation_arities :=
    Continuation.Map.union_total_shared
      (fun cont arity1 arity2 =>
        let! tmp1 := phys_equal arity1 arity2 in
        if tmp1
        then ret arity1
        else
          fatal_errorf2 "Continuation %a was declared several times"
            Continuation.print cont)
      t1.(continuation_arities) t2.(continuation_arities)
  in
  let* continuation_uses :=
    Continuation.Map.union_total
      (fun _ uses1 uses2 => Continuation_uses.union uses1 uses2)
      t1.(continuation_uses) t2.(continuation_uses)
  in
  ret
    {| continuation_uses := continuation_uses;
       continuation_arities := continuation_arities
    |}.

(* 145-148 *)
Definition remove (t : Continuation_uses_env.t) (cont : Continuation.t)
    : M Continuation_uses_env.t :=
  (* PORT-GAP(record-order): the two fields of the record are calls; they
     are taken in the order of the type, the last field first, and each is
     bound before the record is built. *)
  let* continuation_arities :=
    Continuation.Map.remove cont t.(continuation_arities)
  in
  let* continuation_uses :=
    Continuation.Map.remove cont t.(continuation_uses)
  in
  ret
    {| continuation_uses := continuation_uses;
       continuation_arities := continuation_arities
    |}.

(* 150 *)
Definition delete_continuation_uses
    : Continuation_uses_env.t -> Continuation.t -> M Continuation_uses_env.t :=
  remove.

(* 152-158 *)
Definition clear_continuation_uses (t : Continuation_uses_env.t)
    (cont : Continuation.t) : M Continuation_uses_env.t :=
  (* PORT-GAP(papp): [Option.map] is given its first argument only. *)
  let! tmp1 := papp1 Option.map Continuation_uses.clear_uses in
  let! tmp2 := Continuation.Map.update cont tmp1 t.(continuation_uses) in
  ret (update_continuation_uses t tmp2).

(* 160-164 *)
(* PORT-GAP(loose): the record pattern of the parameter is a match, here and
   at [reset_uses]. *)
Definition mark_non_inlinable (t : Continuation_uses_env.t)
    : M Continuation_uses_env.t :=
  match t with
  | {| continuation_uses := continuation_uses;
       continuation_arities := continuation_arities
    |} =>
    let* continuation_uses :=
      Continuation.Map.map Continuation_uses.mark_non_inlinable
        continuation_uses
    in
    ret
      {| continuation_uses := continuation_uses;
         continuation_arities := continuation_arities
      |}
  end.

(* 166-167 *)
Definition reset_uses (t : Continuation_uses_env.t)
    : M Continuation_uses_env.t :=
  match t with
  | {| continuation_uses := _; continuation_arities := continuation_arities |}
    =>
    ret
      {| continuation_uses := Continuation.Map.empty;
         continuation_arities := continuation_arities
      |}
  end.
