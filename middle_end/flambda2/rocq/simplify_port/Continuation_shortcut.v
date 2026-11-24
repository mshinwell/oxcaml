(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Basile Clément, OCamlPro                         *)
(*                                                                        *)
(*   Copyright 2013--2025 OCamlPro SAS                                    *)
(*   Copyright 2014--2025 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/continuation_shortcut.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Continuation Format List Misc
  Or_null Simple Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Or_null.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16-20 *)
Record t : Type := {
  params : Bound_parameters.t;
  continuation : Continuation.t;
  args : list Simple.t
}.

(* 22-33 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept; the
   lines of the format are joined. *)
Definition print (ppf : Format.formatter)
    '({| params := params; continuation := continuation; args := args |} : t)
    : M unit :=
  (* PORT-GAP(papp): 30-32, [Format.pp_print_list] is given its first two
     arguments only. *)
  let! tmp1 :=
    papp2 Format.pp_print_list
      (Some (fun (ppf : Format.formatter) (_ : unit) =>
               Format.fprintf0 ppf ",@ "))
      Simple.print
  in
  Format.fprintf6 ppf
    "@[<hov 1>(@[<hov 1>(params@ %a)@]@ @[<hov 1>(continuation@ %a)@]@ @[<hov 1>(args@ %a)@])@]"
    Bound_parameters.print params Continuation.print continuation tmp1 args.

(* 35 *)
Definition create (params : Bound_parameters.t)
    (continuation : Continuation.t) (args : list Simple.t) : M t :=
  ret {| params := params; continuation := continuation; args := args |}.

(* PORT-GAP(loose): 37, [let continuation { continuation; _ } =
   continuation] is the projection that Rocq makes for the field
   [continuation] of the record (Rocq has one name space for fields and
   functions): it is not in [M], and the extracted file has it after the
   type, before [print]. *)

(* 39-57 *)
Definition apply (t : t) (shortcut_args : list Simple.t)
    : M (Continuation.t * list Simple.t) :=
  (* 39: the record pattern of the first parameter. *)
  let* '{| params := params; continuation := continuation; args := args |} :=
    ret t
  in
  let* subst :=
    let! tmp1 := Bound_parameters.vars params in
    List.fold_left2
      (fun subst param arg => Variable_.Map.add param arg subst)
      Variable_.Map.empty tmp1 shortcut_args
  in
  let! tmp1 :=
    List.map
      (fun arg =>
        Simple.pattern_match' arg
          (fun var coercion =>
            let! tmp2 := Variable_.Map.find_or_null var subst in
            match tmp2 with
            | Or_null.Null => ret arg
            | Or_null.This simple => Simple.apply_coercion_exn simple coercion
            end)
          (fun _ _ => ret arg)
          (fun _ => ret arg))
      args
  in
  ret (continuation, tmp1).

(* 59-63 *)
Definition to_alias (t : t) : M (option Continuation.t) :=
  let* params := Bound_parameters.simples t.(params) in
  let! tmp1 := Misc.Stdlib.List.equal Simple.equal t.(args) params in
  if tmp1 then ret (Some t.(continuation)) else ret None.
