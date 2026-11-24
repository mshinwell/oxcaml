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

(* This file follows middle_end/flambda2/simplify/env/one_continuation_use.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by
   definition under the compiler's names; the numbers in the comments are the
   lines of that file. What is not from that file: the form (the monad, the
   temporaries [tmpN], the arguments by place) is that of GUIDE.md. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation_use_kind
  Downwards_env Flambda2_types Format.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17-18 *)
From SimplifyPort.abbrev.one_continuation_use Require Import Port_abbreviations.
(*OCAML
module DE = Downwards_env
module T = Flambda2_types
OCAML*)

(* 20-25 *)
Record t : Type :=
  { id : Apply_cont_rewrite_id.t;
    kind : Continuation_use_kind.t;
    arg_types : list T.t;
    env : DE.t
  }.

(* 27. In the compiler: [kind ~env_at_use:env id ~arg_types]. *)
Definition create (kind : Continuation_use_kind.t) (env : DE.t)
    (id : Apply_cont_rewrite_id.t) (arg_types : list T.t)
    : M One_continuation_use.t :=
  ret {| id := id; kind := kind; arg_types := arg_types; env := env |}.

(* 29-36 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept, and
   the record pattern of the parameter is a match. *)
Definition print (ppf : Format.formatter) (t : One_continuation_use.t)
    : M unit :=
  match t with
  | {| id := id; kind := _; arg_types := arg_types; env := _ |} =>
    (* PORT-GAP(papp): [Format.pp_print_list] is given its first two
       arguments only. *)
    let! tmp1 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space)
        Flambda2_types.print
    in
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(id %a)@]@ @[<hov 1>(arg_types@ %a)@]@ )@]"
      Apply_cont_rewrite_id.print id tmp1 arg_types
  end.

(* PORT-GAP(loose): 38, [id] is the projection [id] of the record [t]: it
   is pure in Rocq, and Rocq prints it as [let id t = t.id] after the
   type. *)

(* 40 *)
Definition use_kind (t : One_continuation_use.t) : M Continuation_use_kind.t :=
  ret t.(kind).

(* PORT-GAP(loose): 42, [arg_types] is the projection [arg_types] of the
   record [t]: it is pure in Rocq, and Rocq prints it as [let arg_types t =
   t.arg_types] after the type. *)

(* 44 *)
Definition env_at_use (t : One_continuation_use.t) : M DE.t := ret t.(env).

(* PORT-GAP(update): 48, [{ t with kind }]. *)
Definition update_kind (t : One_continuation_use.t)
    (kind : Continuation_use_kind.t) : One_continuation_use.t :=
  {| id := t.(id);
     kind := kind;
     arg_types := t.(arg_types);
     env := t.(env)
  |}.
Extract Inlined Constant update_kind =>
  "(fun t kind -> { t with kind = kind })".

(* 46-49 *)
Definition mark_non_inlinable (t : One_continuation_use.t)
    : M One_continuation_use.t :=
  match t.(kind) with
  | Continuation_use_kind.Inlinable =>
    ret (update_kind t (Continuation_use_kind.Non_inlinable false))
  | Continuation_use_kind.Non_inlinable _ => ret t
  end.
