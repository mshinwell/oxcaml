(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Vincent Laviron, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/comparison_result.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. The file does
   not import Simplify_import, which the compiler's file does not open: its
   abbreviation of a module is its own. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Flambda_kind Flambda_primitive Format Simple
  Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Flambda_primitive.comparison
   Flambda_primitive.comparison_behaviour
   Flambda_primitive.equality_comparison Flambda_primitive.unary_primitive *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
From SimplifyPort.abbrev.comparison_result Require Import Port_abbreviations.
(*OCAML
module P = Flambda_primitive
OCAML*)

(* 17-19. The type has the name of a field of [t]: it gets one [_]. *)
Inductive tagged_or_untagged_ : Type :=
| Tagged
| Untagged.

(* 21-27 *)
Record t : Type := {
  lhs : Simple.t;
  rhs : Simple.t;
  kind : Flambda_kind.Standard_int.t;
  signed : P.signed_or_unsigned;
  tagged_or_untagged : tagged_or_untagged_
}.

(* 29-46 *)
(* PORT-GAP(loose): 30, the attribute [@warning "-fragile-match"] is not
   kept. *)
Definition create (prim : P.t) (comparison_results : Variable_.Map.t t)
    : M (option t) :=
  match prim with
  | P.Binary
      (P.Int_comp kind (P.Yielding_int_like_compare_functions signed)) lhs
      rhs =>
    ret
      (Some
         {| lhs := lhs;
            rhs := rhs;
            kind := kind;
            signed := signed;
            tagged_or_untagged := Untagged
         |})
  | P.Unary P.Tag_immediate arg =>
    let! tmp1 := Simple.must_be_var arg in
    match tmp1 with
    | None => ret None
    | Some (var, _) =>
      let! tmp1 := Variable_.Map.find_opt var comparison_results in
      match tmp1 with
      | None => ret None
      | Some
          {| lhs := lhs;
             rhs := rhs;
             kind := kind;
             signed := signed;
             tagged_or_untagged := Untagged
          |} =>
        ret
          (Some
             {| lhs := lhs;
                rhs := rhs;
                kind := kind;
                signed := signed;
                tagged_or_untagged := Tagged
             |})
      | Some {| tagged_or_untagged := Tagged |} =>
        fatal_errorf2 "Tagging of an already tagged result %a" Variable_.print
          var
      end
    end
  | _ => ret None
  end.

(* 48-63 *)
(* PORT-GAP(loose): 48, the attribute [@ocamlformat "disable"] is not
   kept. *)
Definition print (ppf : Format.formatter)
    '({| lhs := lhs;
         rhs := rhs;
         kind := kind;
         signed := signed;
         tagged_or_untagged := tagged_or_untagged
      |} : t) : M unit :=
  let& prefix := match signed with P.Signed => "" | P.Unsigned => "u" end in
  let& result :=
    match tagged_or_untagged with
    | Tagged => "tagged"
    | Untagged => "untagged"
    end
  in
  Format.fprintf8 ppf
    "@[<hov 1>(@[<hov 1>(lhs@ %a)@]@ @[<hov 1>(rhs@ %a)@]@ @[<hov 1>(kind@ %s%a -> %s)@]@ )@]"
    Simple.print lhs Simple.print rhs prefix
    Flambda_kind.Standard_int.print_lowercase kind result.

(* 65-86 *)
Definition convert_result_compared_to_tagged_zero
    '({| lhs := lhs;
         rhs := rhs;
         kind := kind;
         signed := signed;
         tagged_or_untagged := tagged_or_untagged
      |} as t)
    (op : P.comparison P.signed_or_unsigned) : M (option P.t) :=
  (match tagged_or_untagged with
   | Tagged => ret tt
   | Untagged =>
     fatal_errorf2 "Comparing untagged result with tagged zero: %a" print t
   end) ;;
  (* PORT-GAP(loose): 72, the attribute [@local] is not kept. *)
  let& make_result :=
    fun (new_op : P.comparison P.signed_or_unsigned) =>
    let& prim := P.Int_comp kind (P.Yielding_bool new_op) in
    ret (Some (P.Binary prim lhs rhs))
  in
  (* Only signed comparisons should be transformed. *)
  match op with
  | P.Eq => make_result P.Eq
  | P.Neq => make_result P.Neq
  | P.Lt P.Signed => make_result (P.Lt signed)
  | P.Gt P.Signed => make_result (P.Gt signed)
  | P.Le P.Signed => make_result (P.Le signed)
  | P.Ge P.Signed => make_result (P.Ge signed)
  | P.Lt P.Unsigned => ret None
  | P.Gt P.Unsigned => make_result P.Neq (* compare x y >u 0 <=> x <> y *)
  | P.Le P.Unsigned => make_result P.Eq (* compare x y <=u 0 <=> x = y *)
  | P.Ge P.Unsigned => ret None
  end.
