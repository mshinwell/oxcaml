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

(* This file follows middle_end/flambda2/simplify/are_lifting_conts.ml
   (Git blob c131481d4ff96ab5831dbb41fb70029bf853ab7d), definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the arguments
   by place, the two types kept as OCaml text) is that of GUIDE.md. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Continuation Continuation_uses Format.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16-30. The two types are the compiler's text: [t] has constructors with
   inline records, which Rocq cannot print, and [reason] must stand before
   it. *)
(*OCAML
type reason =
  | At_toplevel
  | In_speculative_inlining
  | In_continuation_specialization
  | In_recursive_continuation
  | In_inlinable_continuation

type t =
  | Not_lifting of reason
  | Analyzing of
      { continuation : Continuation.t;
        is_exn_handler : bool;
        uses : Continuation_uses.t
      }
  | Lifting_out_of of { continuation : Continuation.t }
OCAML*)

(* 16-21 *)
Inductive reason : Type :=
| At_toplevel : reason
| In_speculative_inlining : reason
| In_continuation_specialization : reason
| In_recursive_continuation : reason
| In_inlinable_continuation : reason.
Extract Inductive reason => "reason" [ "At_toplevel" "In_speculative_inlining" "In_continuation_specialization" "In_recursive_continuation" "In_inlinable_continuation" ].

(* 23-30. The fields of the inline records are taken by place, as in
   decl/Are_lifting_conts.v: a constructor is built by a function of the tuple
   of its fields and matched by one function for each constructor. *)
Inductive t : Type :=
| Not_lifting : reason -> t
| Analyzing : Continuation.t -> bool -> Continuation_uses.t -> t
| Lifting_out_of : Continuation.t -> t.
Extract Inductive t => "t" [ "Not_lifting" "(fun (x__1, x__2, x__3) -> (Analyzing { continuation = x__1; is_exn_handler = x__2; uses = x__3 } : t))" "(fun x__1 -> (Lifting_out_of { continuation = x__1 } : t))" ] "(fun f__1 f__2 f__3 x__0 -> match (x__0 : t) with Not_lifting x__1 -> f__1 x__1 | Analyzing { continuation = x__1; is_exn_handler = x__2; uses = x__3 } -> f__2 x__1 x__2 x__3 | Lifting_out_of { continuation = x__1 } -> f__3 x__1)".

(* 32 *)
Definition no_lifting (reason : Are_lifting_conts.reason) : M t :=
  ret (Not_lifting reason).

(* 34-35 *)
Definition think_about_lifting_out_of (is_exn_handler : bool)
    (continuation : Continuation.t) (uses : Continuation_uses.t) : M t :=
  ret (Analyzing continuation is_exn_handler uses).

(* 37 *)
Definition lift_continuations_out_of (continuation : Continuation.t) : M t :=
  ret (Lifting_out_of continuation).

(* 39-49 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept, here
   and at [print]. *)
Definition print_reason (ppf : Format.formatter)
    (reason : Are_lifting_conts.reason) : M unit :=
  match reason with
  | At_toplevel => Format.fprintf0 ppf "at_toplevel"
  | In_speculative_inlining => Format.fprintf0 ppf "in_speculative_inlining"
  | In_continuation_specialization =>
    Format.fprintf0 ppf "in_continuation_specialization"
  | In_recursive_continuation =>
    Format.fprintf0 ppf "in_recursive_continuation"
  | In_inlinable_continuation =>
    Format.fprintf0 ppf "in_inlinable_continuation"
  end.

(* 51-68 *)
Definition print (ppf : Format.formatter) (t : Are_lifting_conts.t) : M unit :=
  match t with
  | Not_lifting reason =>
    Format.fprintf2 ppf "@[<hov>(Not_lifting@ %a)@]" print_reason reason
  | Lifting_out_of continuation =>
    Format.fprintf2 ppf
      "@[<hov>(lifting_out_of@ @[<hov 1>(continuation@ %a)@])@]"
      Continuation.print continuation
  | Analyzing continuation is_exn_handler uses =>
    Format.fprintf5 ppf
      "@[<hov>(analysing@ @[<hov 1>(continuation@ %a)@]@ @[<hov 1>(is_exn_handler@ %b)@]@ @[<hov 1>(uses@ %a)@])@]"
      Continuation.print continuation is_exn_handler Continuation_uses.print
      uses
  end.
