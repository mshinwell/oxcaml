(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)



(* Expanded types, as the model sees them: a type that is not an alias,
   given by its kind and its head.

   This file is to be reviewed, line by line against the module
   [Expanded_type] of middle_end/flambda2/types/expand_head.ml, as
   FlambdaTypeGrammar.v is against type_grammar.ml. It holds definitions
   only and it extracts. Meet works on expanded types
   ([Meet_env.meet_expanded_head], FlambdaMeetEnv.v), and the join that
   meet is given calls it on them.

   What the model has of [Expanded_type]:
   - [descr]: the fifteen constructors, one for each kind, are five
     here, as those of [Type_grammar.t] are in FlambdaTypeGrammar.v: the
     eleven of the naked numbers other than the immediates are the one
     [Head_naked_number], which carries the kind. The type is named
     [head] here, [descr] being the name of the field.
   - [t]: in full, a kind and [Unknown], [Bottom] or a head.
   - [to_type], [of_non_alias_type]: in full, but that a [Simple] has no
     coercion (FlambdaModel.v), so [of_non_alias_type] has no
     [?coercion] and [Type_grammar.apply_coercion_head_of_kind_value]
     is not there. [None] is the fatal error of the compiler for a type
     that is an alias.
   Not here yet, and to come with the functions of meet: [create_const]
   and the other creation functions, [bottom_like], [unknown_like],
   [is_bottom], [is_unknown], [descr_oub]; [expand_head0] and
   [expand_head] themselves.

   Nothing asks that the head of an expanded type be of its kind: the
   compiler's creation functions give that, and [of_non_alias_type]
   here. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar.
Import ListNotations.

(* [Expand_head.Expanded_type]. *)
Module Expanded_type.

  (* [Expanded_type.descr]. *)
  Inductive head : Type :=
    | Head_value (head : head_of_kind_value)
    | Head_naked_immediate (head : head_of_kind_naked_immediate)
    | Head_naked_number (k : naked_number_kind) (head : list Z)
    | Head_rec_info (head : unit)
    | Head_region (head : unit).

  (* [Expanded_type.t]. *)
  Record t : Type := create {
    kind : flambda_kind;
    descr : or_unknown_or_bottom head
  }.

  Definition create_bottom (kind : flambda_kind) : t := create kind Bottom.

  Definition create_unknown (kind : flambda_kind) : t := create kind Unknown.

  (* [Expanded_type.to_type]. *)
  Definition to_type (expanded : t) : flambda_type :=
    match descr expanded with
    | Unknown => unknown (kind expanded)
    | Bottom => bottom (kind expanded)
    | Ok (Head_value head) => Type_value (Ok (No_alias head))
    | Ok (Head_naked_immediate head) =>
      Type_naked_immediate (Ok (No_alias head))
    | Ok (Head_naked_number k head) => Type_naked_number k (Ok (No_alias head))
    | Ok (Head_rec_info head) => Type_rec_info (Ok (No_alias head))
    | Ok (Head_region head) => Type_region (Ok (No_alias head))
    end.

  (* [Expanded_type.of_non_alias_type]. [None] is a fatal error of the
     compiler: the type is an alias. *)
  Definition of_non_alias_type (ty : flambda_type) : option t :=
    let of_descr {A : Type} (k : flambda_kind) (make : A -> head)
        (ty : type_descr A) : option t :=
      match ty with
      | Unknown => Some (create_unknown k)
      | Bottom => Some (create_bottom k)
      | Ok (No_alias head) => Some (create k (Ok (make head)))
      | Ok (Equals _) => None
      end
    in
    match ty with
    | Type_value ty => of_descr Value Head_value ty
    | Type_naked_immediate ty =>
      of_descr (Naked_number Kind_naked_immediate) Head_naked_immediate ty
    | Type_naked_number k ty =>
      of_descr (Naked_number k) (Head_naked_number k) ty
    | Type_rec_info ty => of_descr Rec_info Head_rec_info ty
    | Type_region ty => of_descr Region Head_region ty
    end.

End Expanded_type.
