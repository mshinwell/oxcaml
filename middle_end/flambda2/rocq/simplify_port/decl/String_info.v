(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018--2019 OCamlPro SAS                                    *)
(*   Copyright 2018--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [String_info], after its interface
   middle_end/flambda2/term_basics/string_info.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* string_info.mli:17  type t = string *)
Definition t : Type := string.
Extract Inlined Constant t => "String_info.t".
Module Set_.
  (* string_info.mli:19  include Container_types.S with type t := t *)
  Definition elt : Type := String_info.t.
  Extract Inlined Constant elt => "String_info.Set.elt".
  (* string_info.mli:19  include Container_types.S with type t := t *)
  Parameter t : Type.
  Extract Inlined Constant t => "String_info.Set.t".
  (* string_info.mli:19  include Container_types.S with type t := t *)
  Parameter is_empty : t -> M bool.
  Extract Inlined Constant is_empty => "String_info.Set.is_empty".
  (* string_info.mli:19  include Container_types.S with type t := t *)
  Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  Extract Inlined Constant fold => "String_info.Set.fold".
End Set_.
