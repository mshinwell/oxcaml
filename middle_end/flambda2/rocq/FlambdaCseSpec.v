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

(* Not computing again a primitive that has been computed: a
   normalisation that refines.

   This file is to be reviewed: [share_known_primitives] and what it is
   made of, which are extracted and run by the validation of
   middle_end/flambda2/tests/semantics/; the action of a renaming on
   what the pass knows ([rename_computed]); and the statements.

   Simplify keeps the primitives it has seen applied, each with the
   variable bound to its result, and replaces a later application of the
   same primitive to the same arguments by that variable (common
   subexpression elimination: [Simplify_primitive], with
   [Flambda_primitive.Eligible_for_cse]). A boxed number that is used
   twice is unboxed twice by the front end and once after Simplify; so is
   a comparison or a sum written twice in the source, once a function
   has been inlined.

   [share_known_primitives] does the same with what can be read off the
   term. It goes through a term keeping, for a variable bound by a [Let]
   to a primitive that may be shared ([shareable]) applied to arguments,
   that primitive and those arguments ([computed]). A later [Let] of the
   same primitive applied to the same arguments becomes a [Let] of that
   variable ([share_named]). Nothing else is rewritten, and the [Let]
   stays, as in FlambdaBlockLoadSpec.v and FlambdaUnboxSpec.v, which this
   file follows: what is known of a variable, and what mentions it in an
   argument, is forgotten under a binder of it; a handler of a
   non-recursive continuation is gone into, with what is known where it
   is defined; the handlers of recursive ones and the bodies of code are
   left as they are.

   What may be shared is a choice that is narrower than the compiler's.
   The primitives listed in [shareable] compute a number from numbers,
   or look at a value without reading memory that can change: the
   length of a string is among them, as the compiler shares it too
   ([String_length] has no effects and no coeffects in
   [Flambda_primitive]). Left out: [Opaque_identity], which Simplify
   never shares; [Block_load] and [String_or_bigstring_load], until the
   model says which loads read memory that cannot change; and the
   primitives that allocate ([Box_number], [Make_block]), which the
   compiler does share where what is allocated is immutable.

   CR mshinwell: sharing an allocation makes two values one, which
   physical equality can tell apart. The compiler shares immutable
   allocations all the same. This file does not, so a unit in which
   Simplify shared one is not validated; whether the model should let it
   be is the question of what physical equality says of immutable
   values.

   The result refines the term
   ([share_known_primitives_refines_statement]). It is not claimed to be
   equivalent to it, though it most likely is; a refinement is what the
   term before Simplify needs.

   The pass commutes with the renamings of FlambdaNominalSpec.v, what it
   knows being renamed with the term
   ([share_primitives_knowing_equivariant_statement]): it compares
   variables for equality and makes no name.

   The proofs are in FlambdaCseProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaMapSpec FlambdaPrimitiveModel FlambdaPrimitiveSpec
  FlambdaSemanticsSpec FlambdaNormaliseSpec FlambdaNominalSpec.
Import ListNotations.

(* ======================================================================== *)
(* What is known                                                            *)
(* ======================================================================== *)

(* The primitives whose result may stand for a later application to the
   same arguments. *)
Definition shareable (p : prim) : bool :=
  match p with
  | Unary
      (Is_int _ | Get_tag | Num_conv _ _ | Boolean_not | Unbox_number _
      | Untag_immediate | Tag_immediate | String_length
      | Unary_int_arith _ _) =>
    true
  | Binary (Phys_equal _ | Int_arith _ _ | Int_shift _ _ | Int_comp _ _) =>
    true
  | _ => false
  end.

(* The variables known to hold the result of a primitive, each with the
   primitive and its arguments. *)
Definition computed : Type := list (variable * (prim * list simple)).

(* What is known that does not mention [x]. *)
Definition forget_computed (x : variable) (known : computed) : computed :=
  filter
    (fun entry =>
       negb (Pos.eqb x (fst entry))
       && negb (var_in_simples x (snd (snd entry))))
    known.

(* The same of parameters, bound one after the other. *)
Fixpoint forget_computed_vars (xs : list variable) (known : computed)
    : computed :=
  match xs with
  | [] => known
  | x :: xs => forget_computed_vars xs (forget_computed x known)
  end.

(* What is known in the body of a [Let] of [x] to [d]: nothing that
   mentions the old [x], and that the new one is the result of [d], if
   that is a primitive that may be shared, applied to arguments that do
   not mention the old [x]. *)
Definition computed_under_let (known : computed) (x : variable) (d : named)
    : computed :=
  let known := forget_computed x known in
  match d with
  | Prim p args =>
    if shareable p && negb (var_in_simples x args)
    then (x, (p, args)) :: known
    else known
  | _ => known
  end.

(* ======================================================================== *)
(* Sharing                                                                  *)
(* ======================================================================== *)

Definition same_simples (args args' : list simple) : bool :=
  if list_eq_dec simple_eq_dec args args' then true else false.

(* The first variable known to hold the result of [p] applied to
   [args]. *)
Fixpoint computed_by (known : computed) (p : prim) (args : list simple)
    : option variable :=
  match known with
  | [] => None
  | (x, (p', args')) :: known =>
    if prim_eqb p p' && same_simples args args'
    then Some x
    else computed_by known p args
  end.

Definition share_named (known : computed) (d : named) : named :=
  match d with
  | Prim p args =>
    match computed_by known p args with
    | Some x => Simple (Var x)
    | None => d
    end
  | _ => d
  end.

Fixpoint share_primitives_knowing (known : computed) (e : expr) : expr :=
  match e with
  | Let x kind d body =>
    Let x kind (share_named known d)
      (share_primitives_knowing (computed_under_let known x d) body)
  | Let_static bindings body =>
    Let_static bindings (share_primitives_knowing known body)
  | Let_cont_non_recursive k h body =>
    Let_cont_non_recursive k (share_primitives_in_handler known h)
      (share_primitives_knowing known body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (share_primitives_knowing known body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end
with share_primitives_in_handler (known : computed)
    (h : continuation_handler) : continuation_handler :=
  match h with
  | Handler params metadata handler =>
    Handler params metadata
      (share_primitives_knowing (forget_computed_vars params known) handler)
  end.

Definition share_known_primitives (e : expr) : expr :=
  share_primitives_knowing [] e.

Definition share_known_primitives_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (share_known_primitives e).

(* ======================================================================== *)
(* The pass commutes with renaming                                          *)
(* ======================================================================== *)

(* What is known holds variables: the one bound to each result, and
   those among the arguments. A renaming acts on both. The primitive has
   no name in it. *)
Definition rename_computed (r : renaming) (known : computed) : computed :=
  map
    (fun entry =>
       (rename_variable r (fst entry),
        (fst (snd entry), map (rename_simple r) (snd (snd entry)))))
    known.

(* What is known is renamed with the term. *)
Definition share_primitives_knowing_equivariant_statement : Prop :=
  ∀ (r : renaming) (known : computed) (e : expr),
    share_primitives_knowing (rename_computed r known) (rename_expr r e)
    = rename_expr r (share_primitives_knowing known e).

(* The pass as the validation runs it, with nothing known. *)
Definition share_known_primitives_equivariant_statement : Prop :=
  ∀ (r : renaming) (e : expr),
    share_known_primitives (rename_expr r e)
    = rename_expr r (share_known_primitives e).
