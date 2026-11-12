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


(* Unboxing a parameter of a continuation that is read under a test,
   with a constant given where there is nothing to read: a
   normalisation that refines. It is what the unboxing of a variant
   needs.

   This file is to be reviewed: [unbox_variant_params] and what it is
   made of, and the statement. The validation runs the pass in the
   first phase of its normalisation of the term before
   (FlambdaValidateSpec.normalise_expr_params).

   FlambdaUnboxParamsSpec.v makes a parameter of the [Let] that a
   handler begins with, where that [Let] reads a box which is a
   parameter and every application gives a box that the term shows.
   That is not enough for a variant. The handler of a join of [None]
   and [Some x] begins with [Is_int] of its parameter, which that pass
   unboxes, and then goes by a [Switch] to a continuation that begins
   with the load of the field; and one application gives the constant
   [None], which has no field. Simplify unboxes such a parameter
   ([Unboxing_epa.compute_extra_args_for_variant]): the application
   that gives a block gives its field, and the one that gives a
   constant constructor gives a constant in its place, [poison] of the
   kind of the field ([access_kind_and_poison_const]); for the tag, 0
   ([Tag.Scannable.zero]); for the constant constructor of an
   application that gives a block, 0 as well ([extra_arg_for_ctor]).

   [unbox_variant_params] is made as the other pass is, with the
   differences below. It is not the other pass and more: it takes the
   reads in an order of its own and stops at the first that it cannot
   make a parameter, so it may leave a handler of which the other
   pass makes the first read a parameter (below, at what stops it).

   - The [Let] need not be the first thing in the handler. It is the
     first, going down the handler, that reads a box which is a
     parameter ([first_read]): through the bodies of [Let]s, and
     through the bodies and then the handlers of non-recursive
     [Let_cont]s, as long as no binder on the way binds the parameter
     read or the variable of the [Let]. The variable must not be free
     in the handler ([var_free_b]): it becomes a parameter, in scope
     in all of the handler. The [Let] is removed where it is and its
     variable is the new parameter, the last.

   - The reads are taken in an order ([next_read]): first a [Get_tag],
     then an [Untag_immediate], then an [Is_int], then the loads and
     the unboxings, each sort from the top of the handler down. That
     is the order of Simplify's new parameters for a variant: the tag,
     the constant constructor, whether the value is an immediate, then
     the fields ([Unboxing_epa.add_extra_params_and_args], each
     parameter put before those already there, the fields first). The
     body of a [Let_cont] is gone into before its handler: the front
     end puts the continuation of the first arm of a match outermost,
     and Simplify's parameters for the fields are those of the last
     tag first.

   - Where the [Let] is not the first thing in the handler
     ([extend_args_certain]), an application gets as its new argument:
     a constant of the kind of the [Let] in place of what the read
     would give ([dummy_of]: [poison], or 0 for [Get_tag] and
     [Untag_immediate] at the kind of naked immediates, as Simplify
     gives), if the application does not come to the read
     ([never_reads], below);
     otherwise the constant that the term shows the primitive to give,
     if that is of the kind of the [Let]; or the field of a block that
     a [Let] in scope made, for a load at the kind of values; or the
     number in a box that a [Let] in scope made, for the unboxing of
     such a box at the kind of the number; or the number that a [Let]
     in scope tagged, for the untagging at the kind of naked
     immediates ([certain_projection]); or,
     where the primitive has no value on the argument for the
     parameter read, that constant again. The
     primitive is known to have no value ([no_value_on]) where it is a
     load or [Get_tag] and the argument is a constant, and where it is
     [Untag_immediate] and the argument is a variable that a [Let] in
     scope made a block, or a symbol, which is never an immediate.
     Where the [Let] is the first thing in the
     handler ([head_read]) the argument is the one of the other pass
     ([extend_args]).

   An application does not come to a read ([never_reads]) where the
   term shows it by the constants that the application gives. The
   parameters that it gives a constant naked immediate are known
   ([known_immediates]): whether the value is an immediate and its
   tag, once those are parameters. In the handler each [Switch] on one
   of them is replaced by the arm that it goes to ([take_arms]), and
   the continuations that nothing then applies are removed
   (FlambdaUnusedContsSpec.remove_unused_conts); if what is left of
   the handler is what is left of the handler without the read, up to
   bound names (FlambdaCompareSpec.expr_eqb), the read was in a
   continuation that this application does not reach. That is how the
   application that gives a block of one tag gives [poison] for the
   fields of another: the front end's load says nothing of the tag,
   so it has a value on any block that has the field, and only the
   [Switch] on the tag keeps it from being read.

   Why that constant may be given. The new parameter
   is read only below the place of the [Let] that was removed. In the
   term before, a run that comes to that place evaluates the
   primitive on the parameter read, which no binder on the way has
   bound again, so it is the value that the application gave. The
   constant is given in two cases. In the first, the primitive has no
   value on the argument of the application: such a run of the term
   before is undefined when it comes to the place of the [Let], and a
   refinement asks nothing of the term after; a run that does not
   come to that place does not look at the new parameter. In the
   second, the application does not come to the read: the handler and
   the handler without the read are equivalent under the constants
   that the application gives, since each is equivalent to what is
   left of it (the two rewrites are equivalences where a variable has
   the number it is known to have) and the two that are left are the
   same up to bound names. So nothing is claimed of what a primitive
   does with [poison], and the statement has no premise: the constant
   could be any constant of the kind. It has to be of that kind: a
   handler is applied only to values of the kinds of its parameters
   (FlambdaSemanticsSpec.apply_cont_value), and the run of the term
   before, which may never come to the [Let], does not test anything
   there. That is also why, under a test, the argument given must be
   known to be of the kind of the [Let] whether or not the primitive
   has a value on the box: the field of a block that [Make_block]
   made is of the kind of values, the number in a box that
   [Box_number] made is of the kind of the box, and the number that
   [Tag_immediate] tagged is a naked immediate, as each primitive
   tested when it made the block, the box or the tagged immediate; of
   a field of a static block nothing is tested, so a symbol is not
   taken as a known block here.

   What stops it for a parameter: what stops the other pass; and,
   under a test, an application that may come to the read and whose
   argument is neither known in one of these ways nor one on which
   the primitive has no value. It stops at the first read that it
   cannot make a parameter, and does not look for another. So where
   a handler begins with the load of a field of one parameter and
   then reads the tag of another, and an application gives a block
   that is known for the first and nothing that is known for the
   second, the other pass makes the load a parameter and this one
   makes none: the tag comes first in its order.

   The result refines the term
   ([unbox_variant_params_refines_statement]), under all
   environments; so the pass is for the term before Simplify. It
   makes no name. FlambdaUnboxVariantsRenameSpec.v has the statements
   that it commutes with a renaming and that it keeps scope.

   The proofs are in FlambdaUnboxVariantsProofs.v, which needs no
   review. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel FlambdaMapSpec
  FlambdaPrimitiveModel FlambdaPrimitiveSpec FlambdaSemanticsSpec
  FlambdaNormaliseSpec FlambdaBlockLoadSpec FlambdaUnboxSpec
  FlambdaUnusedContsSpec FlambdaCompareSpec FlambdaUnboxParamsSpec.
Import ListNotations.

(* ======================================================================== *)
(* The argument for a parameter that is read under a test                   *)
(* ======================================================================== *)

(* The constant given where there is nothing to read, of the kind of
   the [Let] that read: what Simplify gives. *)
Definition dummy_of (p : unary_primitive) (kind : flambda_kind) : const :=
  match p with
  | Get_tag | Untag_immediate =>
    if kind_eqb kind (Naked_number Kind_naked_immediate)
    then Naked_immediate 0
    else Poison kind
  | _ => Poison kind
  end.

(* Whether the term shows that the primitive has no value on the
   argument: a load or [Get_tag] of a constant, the untagging of what a
   [Let] in scope made a block, or of a symbol. *)
Definition no_value_on (known : facts) (p : unary_primitive) (arg : simple)
    : bool :=
  match p, arg with
  | (Block_load _ _ _ | Get_tag), Const _ => true
  | Untag_immediate, Var y => is_bound y (known_vars (facts_blocks known))
  | Untag_immediate, Symbol _ => true
  | _, _ => false
  end.

(* The field that a load not marked [Mutable] reads, at the kind of
   values, of a block that a [Let] in scope made. *)
Definition made_field (known : facts) (p : unary_primitive)
    (kind : flambda_kind) (arg : simple) : option simple :=
  match p, arg with
  | Block_load access (Immutable | Immutable_unique) field, Var y =>
    let* block := lookup y (known_vars (facts_blocks known)) in
    let* contents := field_loaded access field block in
    if kind_eqb kind Value then Some contents else None
  | _, _ => None
  end.

(* The number in a box that a [Let] in scope made, for the unboxing of
   a box of that sort, at the kind of the number; and the number that
   a [Let] in scope tagged, for the untagging, at the kind of naked
   immediates. *)
Definition made_number (known : facts) (p : unary_primitive)
    (kind : flambda_kind) (arg : simple) : option simple :=
  match p, arg with
  | Unbox_number boxed, Var y =>
    let* contents := unwrapped (facts_numbers known) (Boxed boxed) (Var y) in
    if kind_eqb kind (unboxed_kind boxed) then Some contents else None
  | Untag_immediate, Var y =>
    let* contents := unwrapped (facts_numbers known) Tagged (Var y) in
    if kind_eqb kind (Naked_number Kind_naked_immediate)
    then Some contents
    else None
  | _, _ => None
  end.

(* What the primitive gives of the argument, where the term shows it and
   shows that it is of the kind given: a constant of that kind, the
   field of a block that was made, or the number that was put in a box
   or tagged. *)
Definition certain_projection (known : facts) (p : unary_primitive)
    (kind : flambda_kind) (arg : simple) : option simple :=
  match projection_of known p arg with
  | Some (Const c) =>
    if kind_eqb (kind_of_const c) kind then Some (Const c) else None
  | Some (Var _ | Symbol _) | None =>
    match made_field known p kind arg with
    | Some contents => Some contents
    | None => made_number known p kind arg
    end
  end.

(* The parameters that an application gives a constant naked immediate,
   with that number. *)
Fixpoint known_immediates (params : list variable) (args : list simple)
    : list (variable * Z) :=
  match params, args with
  | param :: params, Const (Naked_immediate i) :: args =>
    (param, i) :: known_immediates params args
  | _ :: params, _ :: args => known_immediates params args
  | _, _ => []
  end.

(* What is known of the variables that are not bound again. *)
Definition forget_immediates (bound : list variable)
    (consts : list (variable * Z)) : list (variable * Z) :=
  filter (fun entry => negb (among (fst entry) bound)) consts.

(* The expression with each [Switch] on a variable whose number is
   known replaced by the arm that it goes to. *)
Fixpoint take_arms (consts : list (variable * Z)) (e : expr) : expr :=
  match e with
  | Let y kind d body =>
    Let y kind d (take_arms (forget_immediates [y] consts) body)
  | Let_static bindings body => Let_static bindings (take_arms consts body)
  | Let_cont_non_recursive k (Handler handler_params metadata handler) body =>
    Let_cont_non_recursive k
      (Handler handler_params metadata
         (take_arms (forget_immediates handler_params consts) handler))
      (take_arms consts body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (take_arms consts body)
  | Switch (Var t) arms =>
    match lookup t consts with
    | Some i =>
      match find_arm i arms with
      | Some ac => Apply_cont ac
      | None => e
      end
    | None => e
    end
  | Switch (Symbol _ | Const _) _ | Apply _ | Apply_cont _ | Invalid => e
  end.

(* Whether a handler and the handler without one of its reads are the
   same, up to bound names, once the arms that an application takes
   are taken and the continuations that nothing then applies are
   removed: the application does not come to the read. *)
Definition never_reads (consts : list (variable * Z))
    (handler without : expr) : bool :=
  expr_eqb [] []
    (remove_unused_conts (take_arms consts handler))
    (remove_unused_conts (take_arms consts without)).

(* The arguments of an application with one more, the last: the
   constant of [dummy_of], if the application does not come to the
   read, given the handler and the handler without the read; otherwise
   what [p] certainly gives of the argument at position [i]; or, if it
   has no value on it, the constant again. *)
Definition extend_args_certain (params : list variable)
    (handler without : expr) (known : facts) (i : nat) (p : unary_primitive)
    (kind : flambda_kind) (args : list simple) : option (list simple) :=
  let* arg := nth_error args i in
  if never_reads (known_immediates params args) handler without
  then Some (args ++ [Const (dummy_of p kind)])
  else
    match certain_projection known p kind arg with
    | Some projection => Some (args ++ [projection])
    | None =>
      if no_value_on known p arg
      then Some (args ++ [Const (dummy_of p kind)])
      else None
    end.

(* ======================================================================== *)
(* The first read of a parameter                                            *)
(* ======================================================================== *)

(* A [Let] that reads a box: its variable and its kind, the primitive,
   where the parameter read is, and the expression without the [Let]. *)
Record read : Type := Read {
  read_variable : variable;
  read_kind : flambda_kind;
  read_primitive : unary_primitive;
  read_position : nat;
  read_without : expr
}.

(* The sorts of reads, in the order in which they are made
   parameters. *)
Definition reads_tag (p : unary_primitive) : bool :=
  match p with
  | Get_tag => true
  | _ => false
  end.

Definition reads_constant_constructor (p : unary_primitive) : bool :=
  match p with
  | Untag_immediate => true
  | _ => false
  end.

Definition reads_is_int (p : unary_primitive) : bool :=
  match p with
  | Is_int _ => true
  | _ => false
  end.

Definition reads_contents (p : unary_primitive) : bool :=
  match p with
  | Block_load _ _ _ | Unbox_number _ => true
  | _ => false
  end.

Definition reads_any (p : unary_primitive) : bool := true.

(* Whether a [Let] of [f] to [d] reads, by a primitive that is wanted,
   a box which is one of the parameters, neither it nor [f] being among
   the variables bound on the way: the primitive, and where the
   parameter is. *)
Definition param_read (wanted : unary_primitive -> bool)
    (params bound : list variable) (f : variable) (d : named)
    : option (unary_primitive * nat) :=
  match d with
  | Prim (Unary p) [Var x] =>
    if wanted p && reads_a_box p && negb (among x bound)
       && negb (among f bound)
    then option_map (fun i => (p, i)) (position x params)
    else None
  | _ => None
  end.

(* The [Let] that the expression begins with, if it reads a
   parameter. *)
Definition head_read (params : list variable) (e : expr) : option read :=
  match e with
  | Let f kind d rest =>
    let* '(p, i) := param_read reads_any params [] f d in
    Some (Read f kind p i rest)
  | _ => None
  end.

(* The first [Let] that reads a parameter by a primitive that is
   wanted, going down the expression through the bodies of [Let]s and
   through the bodies, then the handlers, of non-recursive [Let_cont]s;
   [bound] is what the binders passed on the way bind. *)
Fixpoint first_read (wanted : unary_primitive -> bool)
    (params bound : list variable) (e : expr) : option read :=
  match e with
  | Let y kind d body =>
    match param_read wanted params bound y d with
    | Some (p, i) => Some (Read y kind p i body)
    | None =>
      let* r := first_read wanted params (y :: bound) body in
      Some
        (Read (read_variable r) (read_kind r) (read_primitive r)
           (read_position r) (Let y kind d (read_without r)))
    end
  | Let_cont_non_recursive k (Handler handler_params metadata handler) body =>
    match first_read wanted params bound body with
    | Some r =>
      Some
        (Read (read_variable r) (read_kind r) (read_primitive r)
           (read_position r)
           (Let_cont_non_recursive k
              (Handler handler_params metadata handler) (read_without r)))
    | None =>
      let* r :=
        first_read wanted params (handler_params ++ bound) handler
      in
      Some
        (Read (read_variable r) (read_kind r) (read_primitive r)
           (read_position r)
           (Let_cont_non_recursive k
              (Handler handler_params metadata (read_without r)) body))
    end
  | Let_static _ _ | Let_cont_recursive _ _ | Apply _ | Apply_cont _
  | Switch _ _ | Invalid =>
    None
  end.

(* The read that is made a parameter next: of the first sort that the
   handler has a read of. *)
Definition next_read (params : list variable) (handler : expr)
    : option read :=
  match first_read reads_tag params [] handler with
  | Some r => Some r
  | None =>
    match first_read reads_constant_constructor params [] handler with
    | Some r => Some r
    | None =>
      match first_read reads_is_int params [] handler with
      | Some r => Some r
      | None => first_read reads_contents params [] handler
      end
    end
  end.

(* How many [Let]s [first_read] may come to: more reads than that are
   not made parameters. *)
Fixpoint lets_in (e : expr) : nat :=
  match e with
  | Let _ _ _ body => S (lets_in body)
  | Let_cont_non_recursive _ (Handler _ _ handler) body =>
    lets_in handler + lets_in body
  | Let_static _ _ | Let_cont_recursive _ _ | Apply _ | Apply_cont _
  | Switch _ _ | Invalid =>
    0
  end.

(* ======================================================================== *)
(* The pass                                                                 *)
(* ======================================================================== *)

(* The [Let_cont] of [k] with the read made a parameter, if the handler
   may take its variable, that variable is not free in the handler, and
   every application in [body] can be given its argument by [extend]. *)
Definition unbox_read
    (extend : facts -> list simple -> option (list simple)) (known : facts)
    (k : continuation) (params : list variable) (metadata : handler_metadata)
    (handler body : expr) (r : read)
    : option (list variable * handler_metadata * expr * expr) :=
  if may_take params metadata (read_variable r)
     && negb (var_free_b (read_variable r) handler)
  then
    let* body := extend_applications_by extend known k body in
    Some
      (params ++ [read_variable r], with_one_more metadata (read_kind r),
       read_without r, body)
  else None.

(* The [Let_cont] of [k], with the reads of its parameters made
   parameters one after the other, in the order of [next_read], as
   long as each can be: if it is the [Let] that the handler begins
   with, as FlambdaUnboxParamsSpec.unbox_heads does it; otherwise with
   arguments that are certain. *)
Fixpoint unbox_reads (fuel : nat) (known : facts) (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler body : expr) : expr :=
  let unchanged :=
    Let_cont_non_recursive k (Handler params metadata handler) body
  in
  match fuel with
  | 0 => unchanged
  | S fuel =>
    let certain (r : read) :=
      unbox_read
        (fun known =>
           extend_args_certain params handler (read_without r) known
             (read_position r) (read_primitive r) (read_kind r))
        known k params metadata handler body r
    in
    let step :=
      let* r := next_read params handler in
      match head_read params handler with
      | Some head =>
        if Pos.eqb (read_variable head) (read_variable r)
        then
          unbox_read
            (fun known =>
               extend_args known (read_position head) (read_primitive head))
            known k params metadata handler body head
        else certain r
      | None => certain r
      end
    in
    match step with
    | Some (params, metadata, handler, body) =>
      unbox_reads fuel known k params metadata handler body
    | None => unchanged
    end
  end.

Fixpoint unbox_variants_knowing (known : facts) (e : expr) : expr :=
  match e with
  | Let x kind d body =>
    Let x kind d (unbox_variants_knowing (facts_under_let known x d) body)
  | Let_static bindings body =>
    Let_static bindings
      (unbox_variants_knowing (facts_under_statics known bindings) body)
  | Let_cont_non_recursive k (Handler params metadata handler) body =>
    let handler :=
      unbox_variants_knowing (facts_under_params known params) handler
    in
    unbox_reads (lets_in handler) known k params metadata handler
      (unbox_variants_knowing known body)
  | Let_cont_recursive handlers body =>
    Let_cont_recursive handlers (unbox_variants_knowing known body)
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => e
  end.

Definition unbox_variant_params (e : expr) : expr :=
  unbox_variants_knowing no_facts e.

Definition unbox_variant_params_refines_statement : Prop :=
  ∀ e : expr, expr_refines e (unbox_variant_params e).
