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


(* Seven bodies of code in which Simplify unboxed a variant that is the
   parameter of a join, and the validation of each once
   [unbox_variant_params] is in the round of the term before.

   This file is to be reviewed: the bodies, against the sources below;
   the round; and the statements.

   [option_heap] is

     external on_heap : 'a -> 'a = "%identity"

     let[@inline never] f : bool -> int -> int =
      fun c x ->
       let v = if c then Some (x + 1) else None in
       match on_heap v with None -> 0 | Some y -> y + 2

   One branch makes the block of [Some] and the other gives the
   constant [None]; the continuation of the [let] tests whether its
   parameter is an immediate and, where it is not, loads the field.
   Simplify gives that continuation two parameters and not the option:
   whether it is an immediate, and the field. The branch of [Some]
   gives 0 and what it computed, and makes no block; the branch of
   [None] gives 1 and the constant [poison] of the kind of values.
   ([on_heap] is there so that the option is not allocated in a
   region: the model has no regions yet. The front end removes it.)

   [list_heap] is the same of a list, [[x + 1]] or [[]], matched by
   [[] -> x + 3 | y :: _ -> y + 2]: both arms of the match are
   continuations, and only the head of the list is read.

   [shape_heap] is

     type shape = Empty | Full | Pair of int * int

     let[@inline never] f : bool -> int -> int =
      fun c x ->
       let v = if c then Pair (x + 1, x) else Full in
       match on_heap v with Empty -> 0 | Full -> 1 | Pair (a, b) -> a + b

   The front end returns the value itself for the two constant
   constructors, so the parameter stays, and the block is still made;
   the continuation gets three more parameters, whether the value is
   an immediate and the two fields, and the branch of [Full] gives
   [poison] for both fields.

   [shape2_heap] is [shape_heap] with [Empty -> 10 | Full -> x + 20]
   for the two constant constructors. The handler then reads which
   constant constructor its parameter is, by an untagging, under the
   test that it is an immediate; Simplify makes that a parameter too,
   the first, and the branch of [Pair] gives 0 for it. The value is
   no longer a parameter and no block is made.

   [nested_heap] is an option of a pair, [Some (x + 1, x)] or [None],
   matched by [None -> 0 | Some (a, b) -> a + b]. Simplify unboxes the
   option and then the pair: the continuation gets whether the value
   is an immediate and the two fields of the pair, and the branch of
   [None] gives [poison] for both. On the term before, the pair is
   first made a parameter, which the branch of [None] gives [poison];
   its two fields are then read from that parameter, and a load has no
   value on the constant [poison] either.

   [either_heap] is

     type either = Left of int | Right of int * int

     let[@inline never] f : bool -> int -> int =
      fun c x ->
       let v = if c then Left (x + 1) else Right (x, x + 2) in
       match on_heap v with Left y -> y + 3 | Right (y, z) -> y + z

   Both branches make a block, of two tags, and the continuation of
   the [let] goes by the tag to the continuation of one constructor,
   which loads its fields. Simplify gives the continuation the tag and
   the fields of both constructors, those of [Right] first, and each
   branch gives [poison] for the fields of the other constructor. The
   loads say nothing of the tag, so the load of the field of [Left]
   has a value on the block of [Right]: here the pass gives [poison]
   because the branch of [Right] gives the tag 1, with which the
   handler does not come to the continuation of [Left]
   (FlambdaUnboxVariantsSpec.never_reads).

   [int64_option_heap] is

     let[@inline never] f : bool -> int64 -> int64 =
      fun c x ->
       let v = if c then Some (add x 1L) else None in
       match on_heap v with None -> 0L | Some y -> add y 2L

   with the arithmetic of %int64_add. The branch of [Some] boxes a
   number and makes the block of it; the continuation of the [let]
   loads the field and unboxes it. Simplify unboxes the option and then
   the number: the continuation gets whether the value is an immediate
   and the number, the branch of [Some] gives the number that it
   computed, and boxes nothing, and the branch of [None] gives [poison]
   of the kind of the number. On the term before, the field is first
   made a parameter, and then its unboxing, which is under the test:
   the branch of [Some] gives the number in the box that it made
   (FlambdaUnboxVariantsSpec.made_number). The two constants [1L] and
   [2L] are symbols that the unit binds to boxed numbers, which the
   body unboxes; they are written here as the numbers, and the boxed
   [0L] that the branch of [None] returns as the symbol 1.

   The bodies are those of the function of each source: the body
   before Simplify and the body after. They are written by hand from
   the two terms that the compiler prints ([-drawfexpr-to] and
   [-dfexpr-to]), because the test tool does not convert the constant
   [poison] yet. The binding of the depth variable of the code, which
   has nothing in the model, is left out; the names are numbered here.

   [round_with_variants] is
   FlambdaUnboxParamsExamplesSpec.round_with_unboxing with
   [unbox_variant_params] for [unbox_known_params]. It is here for the
   examples only; the validation does not run it.

   What is said of each body: the body before, after five such rounds,
   is the body after up to bound names ([..._validated_statement]);
   after five rounds of today it is not
   ([..._not_validated_today_statement]); and the body after refines
   the body before, under all environments ([..._refines_statement]),
   which follows from the first by the theorems of the passes and of
   the comparison. So the constant [poison] that Simplify gives where
   there is no field is where the pass gives it. Of [poison] that says
   what the refinement says and no more: a run of the body before that
   is defined is matched by the body after; where the body before is
   undefined, as it is if it comes to a read that has no value,
   nothing is claimed of the body after.

   The two bodies that FlambdaUnboxParamsExamplesSpec.v validates with
   its round are validated with this one too
   ([earlier_examples_validated_statement]).

   The proofs are in FlambdaUnboxVariantsExamplesProofs.v, which needs
   no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaPrimitiveModel FlambdaSemanticsSpec FlambdaCompareSpec
  FlambdaNormaliseSpec FlambdaBlockLoadSpec FlambdaLoopAliasesSpec
  FlambdaShortcutSpec FlambdaSinkContsSpec FlambdaUnboxSpec
  FlambdaUnusedContsSpec FlambdaUnusedParamsSpec FlambdaValidateSpec
  FlambdaUnboxParamsSpec FlambdaUnboxParamsExamplesSpec
  FlambdaUnboxVariantsSpec.
From OxCamlFlambda2Types Require Import FlambdaAliasesSpec.
Import ListNotations.
Open Scope positive_scope.

(* ======================================================================== *)
(* The round                                                                *)
(* ======================================================================== *)

Definition round_with_variants (e : expr) : expr :=
  let e :=
    shortcut_switches
      (thread_switches
         (inline_tail_conts
            (sink_let_conts
               (remove_unused_conts (collapse_switches (fold_constants e))))))
  in
  let e :=
    unbox_variant_params
      (follow_aliases_in_loops []
         (follow_aliases [] (unbox_known_numbers (load_known_blocks e))))
  in
  drop_unused_params
    (remove_unused_defined_lets [] (remove_unused_lets (fold_constants e))).

(* ======================================================================== *)
(* What the bodies are made of                                              *)
(* ======================================================================== *)

(* The test that the match of a variant begins with. *)
Definition is_int (s : simple) : named := Prim (Unary (Is_int true)) [s].

Definition tag_immediate (s : simple) : named :=
  Prim (Unary Tag_immediate) [s].

Definition block_of_one (contents : simple) : named :=
  Prim (Variadic (Make_block (Block_kind_values 0))) [contents].

Definition naked (i : Z) : simple := Const (Naked_immediate i).

Definition poison_value : simple := Const (Poison Value).

(* In each body the parameters of the code are [c], 1, and [x], 2, and
   its return continuation is 1. The continuation of the join is 2,
   its parameter is 3, and the continuations of the branch that makes
   a block are 3 and 4. *)

(* ======================================================================== *)
(* An option                                                                *)
(* ======================================================================== *)

Definition option_heap_before : expr :=
  Let_cont_non_recursive 2
    (Handler [3] (make_handler_metadata [Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let 4 Value (field 0 3)
                (Let 5 Value (add_tagged (Var 4) (tagged 2))
                   (Apply_cont (jump 1 [Var 5])))))
          (Let 6 naked_immediate (is_int (Var 3))
             (Let 7 Value (tag_immediate (Var 6))
                (Let_cont_non_recursive 6
                   (Handler [] (make_handler_metadata [])
                      (Apply_cont (jump 5 [])))
                   (Let 8 naked_immediate (untag (Var 7))
                      (Switch (Var 8)
                         [(0%Z, jump 6 []); (1%Z, jump 1 [tagged 0])])))))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 9 Value (add_tagged (Var 2) (tagged 1))
             (Let 10 Value (block_of_one (Var 9))
                (Apply_cont (jump 2 [Var 10])))))
       (Let_cont_non_recursive 4
          (Handler [] (make_handler_metadata []) (Apply_cont (jump 3 [])))
          (Let 11 naked_immediate (untag (Var 1))
             (Switch (Var 11) [(0%Z, jump 2 [tagged 0]); (1%Z, jump 4 [])])))).

Definition option_heap_after : expr :=
  Let_cont_non_recursive 2
    (Handler [6; 4] (make_handler_metadata [naked_immediate; Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let 5 Value (add_tagged (Var 4) (tagged 2))
                (Apply_cont (jump 1 [Var 5]))))
          (Switch (Var 6) [(0%Z, jump 5 []); (1%Z, jump 1 [tagged 0])])))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 9 Value (add_tagged (Var 2) (tagged 1))
             (Apply_cont (jump 2 [naked 0; Var 9]))))
       (Let 11 naked_immediate (untag (Var 1))
          (Switch (Var 11)
             [(0%Z, jump 2 [naked 1; poison_value]); (1%Z, jump 3 [])]))).

Definition option_heap_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants option_heap_before)
    option_heap_after
  = true.

Definition option_heap_not_validated_today_statement : Prop :=
  expr_eqb [] [] (iterate 5 normalise_expr_before option_heap_before)
    option_heap_after
  = false.

Definition option_heap_refines_statement : Prop :=
  expr_refines option_heap_before option_heap_after.

(* ======================================================================== *)
(* A list                                                                   *)
(* ======================================================================== *)

Definition list_heap_before : expr :=
  Let_cont_non_recursive 2
    (Handler [3] (make_handler_metadata [Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let 9 Value (add_tagged (Var 2) (tagged 3))
                (Apply_cont (jump 1 [Var 9]))))
          (Let_cont_non_recursive 6
             (Handler [] (make_handler_metadata [])
                (Let 7 Value (field 0 3)
                   (Let 8 Value (add_tagged (Var 7) (tagged 2))
                      (Apply_cont (jump 1 [Var 8])))))
             (Let 4 naked_immediate (is_int (Var 3))
                (Let 5 Value (tag_immediate (Var 4))
                   (Let_cont_non_recursive 7
                      (Handler [] (make_handler_metadata [])
                         (Apply_cont (jump 6 [])))
                      (Let_cont_non_recursive 8
                         (Handler [] (make_handler_metadata [])
                            (Apply_cont (jump 5 [])))
                         (Let 6 naked_immediate (untag (Var 5))
                            (Switch (Var 6)
                               [(0%Z, jump 7 []); (1%Z, jump 8 [])])))))))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 10 Value (add_tagged (Var 2) (tagged 1))
             (Let 11 Value (pair (Var 10) (tagged 0))
                (Apply_cont (jump 2 [Var 11])))))
       (Let_cont_non_recursive 4
          (Handler [] (make_handler_metadata []) (Apply_cont (jump 3 [])))
          (Let 12 naked_immediate (untag (Var 1))
             (Switch (Var 12) [(0%Z, jump 2 [tagged 0]); (1%Z, jump 4 [])])))).

Definition list_heap_after : expr :=
  Let_cont_non_recursive 2
    (Handler [4; 7] (make_handler_metadata [naked_immediate; Value])
       (Let_cont_non_recursive 6
          (Handler [] (make_handler_metadata [])
             (Let 8 Value (add_tagged (Var 7) (tagged 2))
                (Apply_cont (jump 1 [Var 8]))))
          (Let_cont_non_recursive 5
             (Handler [] (make_handler_metadata [])
                (Let 9 Value (add_tagged (Var 2) (tagged 3))
                   (Apply_cont (jump 1 [Var 9]))))
             (Switch (Var 4) [(0%Z, jump 6 []); (1%Z, jump 5 [])]))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 10 Value (add_tagged (Var 2) (tagged 1))
             (Apply_cont (jump 2 [naked 0; Var 10]))))
       (Let 12 naked_immediate (untag (Var 1))
          (Switch (Var 12)
             [(0%Z, jump 2 [naked 1; poison_value]); (1%Z, jump 3 [])]))).

Definition list_heap_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants list_heap_before)
    list_heap_after
  = true.

Definition list_heap_not_validated_today_statement : Prop :=
  expr_eqb [] [] (iterate 5 normalise_expr_before list_heap_before)
    list_heap_after
  = false.

Definition list_heap_refines_statement : Prop :=
  expr_refines list_heap_before list_heap_after.

(* ======================================================================== *)
(* Two constant constructors and a pair                                     *)
(* ======================================================================== *)

Definition shape_heap_before : expr :=
  Let_cont_non_recursive 2
    (Handler [3] (make_handler_metadata [Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Apply_cont (jump 1 [Var 3])))
          (Let_cont_non_recursive 6
             (Handler [] (make_handler_metadata [])
                (Let 7 Value (field 1 3)
                   (Let 8 Value (field 0 3)
                      (Let 9 Value (add_tagged (Var 8) (Var 7))
                         (Apply_cont (jump 1 [Var 9]))))))
             (Let 4 naked_immediate (is_int (Var 3))
                (Let 5 Value (tag_immediate (Var 4))
                   (Let_cont_non_recursive 7
                      (Handler [] (make_handler_metadata [])
                         (Apply_cont (jump 6 [])))
                      (Let_cont_non_recursive 8
                         (Handler [] (make_handler_metadata [])
                            (Apply_cont (jump 5 [])))
                         (Let 6 naked_immediate (untag (Var 5))
                            (Switch (Var 6)
                               [(0%Z, jump 7 []); (1%Z, jump 8 [])])))))))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 10 Value (add_tagged (Var 2) (tagged 1))
             (Let 11 Value (pair (Var 10) (Var 2))
                (Apply_cont (jump 2 [Var 11])))))
       (Let_cont_non_recursive 4
          (Handler [] (make_handler_metadata []) (Apply_cont (jump 3 [])))
          (Let 12 naked_immediate (untag (Var 1))
             (Switch (Var 12) [(0%Z, jump 2 [tagged 1]); (1%Z, jump 4 [])])))).

Definition shape_heap_after : expr :=
  Let_cont_non_recursive 2
    (Handler [3; 4; 7; 8]
       (make_handler_metadata [Value; naked_immediate; Value; Value])
       (Let_cont_non_recursive 6
          (Handler [] (make_handler_metadata [])
             (Let 9 Value (add_tagged (Var 8) (Var 7))
                (Apply_cont (jump 1 [Var 9]))))
          (Switch (Var 4) [(0%Z, jump 6 []); (1%Z, jump 1 [Var 3])])))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 10 Value (add_tagged (Var 2) (tagged 1))
             (Let 11 Value (pair (Var 10) (Var 2))
                (Apply_cont (jump 2 [Var 11; naked 0; Var 2; Var 10])))))
       (Let 12 naked_immediate (untag (Var 1))
          (Switch (Var 12)
             [(0%Z, jump 2 [tagged 1; naked 1; poison_value; poison_value]);
              (1%Z, jump 3 [])]))).

Definition shape_heap_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants shape_heap_before)
    shape_heap_after
  = true.

Definition shape_heap_not_validated_today_statement : Prop :=
  expr_eqb [] [] (iterate 5 normalise_expr_before shape_heap_before)
    shape_heap_after
  = false.

Definition shape_heap_refines_statement : Prop :=
  expr_refines shape_heap_before shape_heap_after.

(* ======================================================================== *)
(* Two constant constructors that are told apart, and a pair                *)
(* ======================================================================== *)

Definition shape2_heap_before : expr :=
  Let_cont_non_recursive 2
    (Handler [3] (make_handler_metadata [Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let_cont_non_recursive 9
                (Handler [] (make_handler_metadata [])
                   (Let 11 Value (add_tagged (Var 2) (tagged 20))
                      (Apply_cont (jump 1 [Var 11]))))
                (Let_cont_non_recursive 10
                   (Handler [] (make_handler_metadata [])
                      (Apply_cont (jump 9 [])))
                   (Let 10 naked_immediate (untag (Var 3))
                      (Switch (Var 10)
                         [(0%Z, jump 1 [tagged 10]); (1%Z, jump 10 [])])))))
          (Let_cont_non_recursive 6
             (Handler [] (make_handler_metadata [])
                (Let 7 Value (field 1 3)
                   (Let 8 Value (field 0 3)
                      (Let 9 Value (add_tagged (Var 8) (Var 7))
                         (Apply_cont (jump 1 [Var 9]))))))
             (Let 4 naked_immediate (is_int (Var 3))
                (Let 5 Value (tag_immediate (Var 4))
                   (Let_cont_non_recursive 7
                      (Handler [] (make_handler_metadata [])
                         (Apply_cont (jump 6 [])))
                      (Let_cont_non_recursive 8
                         (Handler [] (make_handler_metadata [])
                            (Apply_cont (jump 5 [])))
                         (Let 6 naked_immediate (untag (Var 5))
                            (Switch (Var 6)
                               [(0%Z, jump 7 []); (1%Z, jump 8 [])])))))))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 12 Value (add_tagged (Var 2) (tagged 1))
             (Let 13 Value (pair (Var 12) (Var 2))
                (Apply_cont (jump 2 [Var 13])))))
       (Let_cont_non_recursive 4
          (Handler [] (make_handler_metadata []) (Apply_cont (jump 3 [])))
          (Let 14 naked_immediate (untag (Var 1))
             (Switch (Var 14) [(0%Z, jump 2 [tagged 1]); (1%Z, jump 4 [])])))).

Definition shape2_heap_after : expr :=
  Let_cont_non_recursive 2
    (Handler [10; 4; 7; 8]
       (make_handler_metadata
          [naked_immediate; naked_immediate; Value; Value])
       (Let_cont_non_recursive 6
          (Handler [] (make_handler_metadata [])
             (Let 9 Value (add_tagged (Var 8) (Var 7))
                (Apply_cont (jump 1 [Var 9]))))
          (Let_cont_non_recursive 5
             (Handler [] (make_handler_metadata [])
                (Let_cont_non_recursive 9
                   (Handler [] (make_handler_metadata [])
                      (Let 11 Value (add_tagged (Var 2) (tagged 20))
                         (Apply_cont (jump 1 [Var 11]))))
                   (Switch (Var 10)
                      [(0%Z, jump 1 [tagged 10]); (1%Z, jump 9 [])])))
             (Switch (Var 4) [(0%Z, jump 6 []); (1%Z, jump 5 [])]))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 12 Value (add_tagged (Var 2) (tagged 1))
             (Apply_cont (jump 2 [naked 0; naked 0; Var 2; Var 12]))))
       (Let 14 naked_immediate (untag (Var 1))
          (Switch (Var 14)
             [(0%Z, jump 2 [naked 1; naked 1; poison_value; poison_value]);
              (1%Z, jump 3 [])]))).

Definition shape2_heap_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants shape2_heap_before)
    shape2_heap_after
  = true.

Definition shape2_heap_not_validated_today_statement : Prop :=
  expr_eqb [] [] (iterate 5 normalise_expr_before shape2_heap_before)
    shape2_heap_after
  = false.

Definition shape2_heap_refines_statement : Prop :=
  expr_refines shape2_heap_before shape2_heap_after.

(* ======================================================================== *)
(* An option of a pair                                                      *)
(* ======================================================================== *)

Definition nested_heap_before : expr :=
  Let_cont_non_recursive 2
    (Handler [3] (make_handler_metadata [Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let 7 Value (field 0 3)
                (Let 8 Value (field 1 7)
                   (Let 9 Value (field 0 7)
                      (Let 10 Value (add_tagged (Var 9) (Var 8))
                         (Apply_cont (jump 1 [Var 10])))))))
          (Let 4 naked_immediate (is_int (Var 3))
             (Let 5 Value (tag_immediate (Var 4))
                (Let_cont_non_recursive 6
                   (Handler [] (make_handler_metadata [])
                      (Apply_cont (jump 5 [])))
                   (Let 6 naked_immediate (untag (Var 5))
                      (Switch (Var 6)
                         [(0%Z, jump 6 []); (1%Z, jump 1 [tagged 0])])))))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 11 Value (add_tagged (Var 2) (tagged 1))
             (Let 12 Value (pair (Var 11) (Var 2))
                (Let 13 Value (block_of_one (Var 12))
                   (Apply_cont (jump 2 [Var 13]))))))
       (Let_cont_non_recursive 4
          (Handler [] (make_handler_metadata []) (Apply_cont (jump 3 [])))
          (Let 14 naked_immediate (untag (Var 1))
             (Switch (Var 14) [(0%Z, jump 2 [tagged 0]); (1%Z, jump 4 [])])))).

Definition nested_heap_after : expr :=
  Let_cont_non_recursive 2
    (Handler [4; 8; 9] (make_handler_metadata [naked_immediate; Value; Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let 10 Value (add_tagged (Var 9) (Var 8))
                (Apply_cont (jump 1 [Var 10]))))
          (Switch (Var 4) [(0%Z, jump 5 []); (1%Z, jump 1 [tagged 0])])))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 11 Value (add_tagged (Var 2) (tagged 1))
             (Apply_cont (jump 2 [naked 0; Var 2; Var 11]))))
       (Let 14 naked_immediate (untag (Var 1))
          (Switch (Var 14)
             [(0%Z, jump 2 [naked 1; poison_value; poison_value]);
              (1%Z, jump 3 [])]))).

Definition nested_heap_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants nested_heap_before)
    nested_heap_after
  = true.

Definition nested_heap_not_validated_today_statement : Prop :=
  expr_eqb [] [] (iterate 5 normalise_expr_before nested_heap_before)
    nested_heap_after
  = false.

Definition nested_heap_refines_statement : Prop :=
  expr_refines nested_heap_before nested_heap_after.

(* ======================================================================== *)
(* Two constructors that hold fields                                        *)
(* ======================================================================== *)

Definition get_tag (s : simple) : named := Prim (Unary Get_tag) [s].

Definition block_of_two (tag : Z) (first second : simple) : named :=
  Prim (Variadic (Make_block (Block_kind_values tag))) [first; second].

Definition either_heap_before : expr :=
  Let_cont_non_recursive 2
    (Handler [3] (make_handler_metadata [Value])
       (Let_cont_non_recursive 7
          (Handler [] (make_handler_metadata [])
             (Let 10 Value (field 0 3)
                (Let 11 Value (add_tagged (Var 10) (tagged 3))
                   (Apply_cont (jump 1 [Var 11])))))
          (Let_cont_non_recursive 8
             (Handler [] (make_handler_metadata [])
                (Let 7 Value (field 1 3)
                   (Let 8 Value (field 0 3)
                      (Let 9 Value (add_tagged (Var 8) (Var 7))
                         (Apply_cont (jump 1 [Var 9]))))))
             (Let 4 naked_immediate (get_tag (Var 3))
                (Let 5 Value (tag_immediate (Var 4))
                   (Let 6 naked_immediate (untag (Var 5))
                      (Switch (Var 6)
                         [(0%Z, jump 7 []); (1%Z, jump 8 [])])))))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 12 Value (add_tagged (Var 2) (tagged 1))
             (Let 13 Value (block_of_one (Var 12))
                (Apply_cont (jump 2 [Var 13])))))
       (Let_cont_non_recursive 4
          (Handler [] (make_handler_metadata [])
             (Let 14 Value (add_tagged (Var 2) (tagged 2))
                (Let 15 Value (block_of_two 1 (Var 2) (Var 14))
                   (Apply_cont (jump 2 [Var 15])))))
          (Let_cont_non_recursive 5
             (Handler [] (make_handler_metadata [])
                (Apply_cont (jump 4 [])))
             (Let_cont_non_recursive 6
                (Handler [] (make_handler_metadata [])
                   (Apply_cont (jump 3 [])))
                (Let 16 naked_immediate (untag (Var 1))
                   (Switch (Var 16)
                      [(0%Z, jump 5 []); (1%Z, jump 6 [])])))))).

Definition either_heap_after : expr :=
  Let_cont_non_recursive 2
    (Handler [4; 7; 8; 10]
       (make_handler_metadata [naked_immediate; Value; Value; Value])
       (Let_cont_non_recursive 7
          (Handler [] (make_handler_metadata [])
             (Let 11 Value (add_tagged (Var 10) (tagged 3))
                (Apply_cont (jump 1 [Var 11]))))
          (Let_cont_non_recursive 8
             (Handler [] (make_handler_metadata [])
                (Let 9 Value (add_tagged (Var 8) (Var 7))
                   (Apply_cont (jump 1 [Var 9]))))
             (Switch (Var 4) [(0%Z, jump 7 []); (1%Z, jump 8 [])]))))
    (Let_cont_non_recursive 4
       (Handler [] (make_handler_metadata [])
          (Let 14 Value (add_tagged (Var 2) (tagged 2))
             (Apply_cont (jump 2 [naked 1; Var 14; Var 2; poison_value]))))
       (Let_cont_non_recursive 3
          (Handler [] (make_handler_metadata [])
             (Let 12 Value (add_tagged (Var 2) (tagged 1))
                (Apply_cont
                   (jump 2 [naked 0; poison_value; poison_value; Var 12]))))
          (Let 16 naked_immediate (untag (Var 1))
             (Switch (Var 16) [(0%Z, jump 4 []); (1%Z, jump 3 [])])))).

Definition either_heap_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants either_heap_before)
    either_heap_after
  = true.

Definition either_heap_not_validated_today_statement : Prop :=
  expr_eqb [] [] (iterate 5 normalise_expr_before either_heap_before)
    either_heap_after
  = false.

Definition either_heap_refines_statement : Prop :=
  expr_refines either_heap_before either_heap_after.

(* ======================================================================== *)
(* An option of a boxed number                                              *)
(* ======================================================================== *)

Definition poison_int64 : simple := Const (Poison naked_int64).

Definition int64_option_heap_before : expr :=
  Let_cont_non_recursive 2
    (Handler [3] (make_handler_metadata [Value])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let 4 Value (field 0 3)
                (Let 12 naked_int64 (unbox_int64 (Var 4))
                   (Let 13 naked_int64
                      (int64_arith Add (Var 12) (Const (Naked_int64 2)))
                      (Let 5 Value (box_int64 (Var 13))
                         (Apply_cont (jump 1 [Var 5])))))))
          (Let 6 naked_immediate (is_int (Var 3))
             (Let 7 Value (tag_immediate (Var 6))
                (Let_cont_non_recursive 6
                   (Handler [] (make_handler_metadata [])
                      (Apply_cont (jump 5 [])))
                   (Let 8 naked_immediate (untag (Var 7))
                      (Switch (Var 8)
                         [(0%Z, jump 6 []); (1%Z, jump 1 [Symbol 1])])))))))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 14 naked_int64 (unbox_int64 (Var 2))
             (Let 15 naked_int64
                (int64_arith Add (Var 14) (Const (Naked_int64 1)))
                (Let 9 Value (box_int64 (Var 15))
                   (Let 10 Value (block_of_one (Var 9))
                      (Apply_cont (jump 2 [Var 10])))))))
       (Let_cont_non_recursive 4
          (Handler [] (make_handler_metadata []) (Apply_cont (jump 3 [])))
          (Let 11 naked_immediate (untag (Var 1))
             (Switch (Var 11) [(0%Z, jump 2 [tagged 0]); (1%Z, jump 4 [])])))).

Definition int64_option_heap_after : expr :=
  Let_cont_non_recursive 2
    (Handler [6; 12] (make_handler_metadata [naked_immediate; naked_int64])
       (Let_cont_non_recursive 5
          (Handler [] (make_handler_metadata [])
             (Let 13 naked_int64
                (int64_arith Add (Var 12) (Const (Naked_int64 2)))
                (Let 5 Value (box_int64 (Var 13))
                   (Apply_cont (jump 1 [Var 5])))))
          (Switch (Var 6) [(0%Z, jump 5 []); (1%Z, jump 1 [Symbol 1])])))
    (Let_cont_non_recursive 3
       (Handler [] (make_handler_metadata [])
          (Let 14 naked_int64 (unbox_int64 (Var 2))
             (Let 15 naked_int64
                (int64_arith Add (Var 14) (Const (Naked_int64 1)))
                (Apply_cont (jump 2 [naked 0; Var 15])))))
       (Let 11 naked_immediate (untag (Var 1))
          (Switch (Var 11)
             [(0%Z, jump 2 [naked 1; poison_int64]); (1%Z, jump 3 [])]))).

Definition int64_option_heap_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants int64_option_heap_before)
    int64_option_heap_after
  = true.

Definition int64_option_heap_not_validated_today_statement : Prop :=
  expr_eqb [] [] (iterate 5 normalise_expr_before int64_option_heap_before)
    int64_option_heap_after
  = false.

Definition int64_option_heap_refines_statement : Prop :=
  expr_refines int64_option_heap_before int64_option_heap_after.

(* ======================================================================== *)
(* The bodies of the other file                                             *)
(* ======================================================================== *)

Definition earlier_examples_validated_statement : Prop :=
  expr_eqb [] [] (iterate 5 round_with_variants pair_computed_before)
    pair_computed_after
  = true
  ∧ expr_eqb [] [] (iterate 5 round_with_variants int64_built_before)
      int64_built_after
    = true.
