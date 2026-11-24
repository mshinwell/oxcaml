(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*   Copyright 2021--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/env/closure_info.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the arguments
   by place, the two types kept as OCaml text) is that of GUIDE.md. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Continuation Format Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* PORT-GAP(verbatim): 16-25 and 65-67, the two types are the compiler's
   text: [t] has a constructor with an inline record, which Rocq cannot
   print; [in_or_out_of_closure] has the name of a function of the file and
   a constructor of [t], so Rocq cannot print it under its name. Both stand
   at the head of the extracted file; in the compiler the second one is
   after [in_a_closure]. *)
(*OCAML
type t =
  | Not_in_a_closure
  | In_a_set_of_closures_but_not_yet_in_a_specific_closure
  | Closure of
      { code_id : Code_id.t;
        return_continuation : Continuation.t;
        exn_continuation : Continuation.t;
        my_closure : Variable.t;
        my_alloc_region : Variable.t
      }

type in_or_out_of_closure =
  | In_a_closure
  | Not_in_a_closure
OCAML*)

(* PORT-GAP(type): 16-25, the fields of the inline record are taken by
   place, as in decl/Closure_info.v: the constructor is built by a function
   of the tuple of its fields, and the type is matched by one function for
   each constructor. *)
Inductive t : Type :=
| Not_in_a_closure : t
| In_a_set_of_closures_but_not_yet_in_a_specific_closure : t
| Closure :
    Code_id.t -> Continuation.t -> Continuation.t -> Variable_.t ->
    Variable_.t -> t.
Extract Inductive t => "t" [ "(Not_in_a_closure : t)" "In_a_set_of_closures_but_not_yet_in_a_specific_closure" "(fun (x__1, x__2, x__3, x__4, x__5) -> (Closure { code_id = x__1; return_continuation = x__2; exn_continuation = x__3; my_closure = x__4; my_alloc_region = x__5 } : t))" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : t) with Not_in_a_closure -> f__1 () | In_a_set_of_closures_but_not_yet_in_a_specific_closure -> f__2 () | Closure { code_id = x__1; return_continuation = x__2; exn_continuation = x__3; my_closure = x__4; my_alloc_region = x__5 } -> f__3 x__1 x__2 x__3 x__4 x__5)".

(* 27-48. PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not
   kept. *)
Definition print (ppf : Format.formatter) (t : Closure_info.t) : M unit :=
  match t with
  | Not_in_a_closure => Format.fprintf0 ppf "not_in_a_closure"
  | In_a_set_of_closures_but_not_yet_in_a_specific_closure =>
    Format.fprintf0 ppf "in_a_set_of_closures"
  | Closure code_id return_continuation exn_continuation my_closure
      my_alloc_region =>
    Format.fprintf10 ppf
      "@[<hov 1>(@[<hov 1>(code_id@ %a)@]@ @[<hov 1>(return_continuation@ %a)@]@ @[<hov 1>(exn_continuation@ %a)@]@ @[<hov 1>(my_closure@ %a)@]@ @[<hov 1>(my_alloc_region@ %a)@])@]"
      Code_id.print code_id Continuation.print return_continuation
      Continuation.print exn_continuation Variable_.print my_closure
      Variable_.print my_alloc_region
  end.

(* 50 *)
Definition not_in_a_closure : t := Not_in_a_closure.

(* 52-53 *)
Definition in_a_set_of_closures : t :=
  In_a_set_of_closures_but_not_yet_in_a_specific_closure.

(* 55-63 *)
Definition in_a_closure (code_id : Code_id.t)
    (return_continuation exn_continuation : Continuation.t)
    (my_closure my_alloc_region : Variable_.t) : M t :=
  ret
    (Closure code_id return_continuation exn_continuation my_closure
       my_alloc_region).

(* PORT-GAP(type): 65-67, the type has the name of the function of line 69
   and its second constructor that of the first constructor of [t]: in Rocq
   each gets one [_], as in decl/Closure_info.v, and the extraction is told
   the compiler's names. *)
Inductive in_or_out_of_closure_ : Type :=
| In_a_closure : in_or_out_of_closure_
| Not_in_a_closure_ : in_or_out_of_closure_.
Extract Inductive in_or_out_of_closure_ => "in_or_out_of_closure" [ "In_a_closure" "(Not_in_a_closure : in_or_out_of_closure)" ].

(* 69-76 *)
Definition in_or_out_of_closure (t : Closure_info.t)
    : M in_or_out_of_closure_ :=
  match t with
  | Not_in_a_closure => ret Not_in_a_closure_
  | Closure _ _ _ _ _ => ret In_a_closure
  | In_a_set_of_closures_but_not_yet_in_a_specific_closure =>
    fatal_errorf0
      "Expected to be either inside or outside a closure, but not [In_a_set_of_closures_but_not_yet_in_a_specific_closure]"
  end.
