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

(* Where static bindings may be: the well-formedness of a compilation unit.

   This file is to be reviewed: [statics_at_toplevel] against the
   definition of toplevel in Simplify
   (simplify/simplify_let_cont_expr.ml, at_unit_toplevel, and
   Downwards_env.at_unit_toplevel), [sets_well_formed] against what the
   compiler checks of a set of closures (terms/static_const.ml,
   match_against_bound_static_pattern) and what it assumes
   (terms/function_declarations.ml, create), [numbers_in_range] against
   the types of the compiler's numbers (the comment of its section says
   which), [well_formed_unit], and the two statements.

   Flambda permits a [Let_static] at the toplevel of a compilation unit
   only, so that it is executed once, before anything that follows it.
   Toplevel is:
   - the unit itself;
   - the body of a [Let], of a [Let_static] or of a [Let_cont] that is at
     toplevel;
   - the handler of a non-recursive continuation bound at toplevel, which
     is not an exception handler, when all its body can do is to apply
     that continuation or raise to the exception continuation of the
     unit: the handler then postdominates its body.
   Nothing else is: not the handler of a recursive continuation, which may
   run many times, and never the body of code, which runs once for each
   call.

   [statics_at_toplevel] is this as a check, carrying down the term
   whether it is at toplevel, as Simplify does. [well_formed_unit] asks
   also that no code id or symbol is bound twice, that the sets of
   closures of the unit are whole ([sets_well_formed]), and that its
   numbers are in range ([numbers_in_range]).

   The model can express sets of closures that the compiler does not
   make (FlambdaSemanticsSpec.v says what the machine does with them).
   [sets_well_formed] is what the compiler's sets have that the model's
   may lack:
   - a closure is at a function slot of its set, and the function slots
     of a set are distinct;
   - the functions of a set have each their own code id. The compiler
     builds a set in which two have the same, and Simplify fails on it;
     such a term is not well-formed Flambda 2 (the human's ruling);
   - the closures of a static set are bound together. The compiler binds
     them with one pattern; here each symbol has a binding of its own,
     which repeats the set and the symbols of its closures, and the
     check is that one group has the binding of each symbol of the set,
     all with the same set;
   - the static sets that one group binds have no code in common, be
     they of one function or of several. Simplify fails on a group two
     of whose sets have the same code.
   It does not ask that the value slots of a set are distinct (the
   compiler's are a map), nor that a code id is named by one set only:
   two sets of a unit may have the same code, unless they are static
   and one group binds them both.
   FlambdaClosuresSpec.v says what follows for a well-formed unit: it
   never makes a closure at a slot its set has not got, and the symbols
   of a static set are bound to its closures in every state of its run.

   The machine enforces the part of this that keeps a static binding from
   being executed more than once. Calling code whose body binds something
   static is undefined, as is a [Let_cont_recursive] one of whose handlers
   does (FlambdaSemanticsSpec.binds_statics); and binding a name that is
   bound already is undefined
   (FlambdaSemanticsSpec.eval_static_bindings). It follows, for any term,
   that what a code id or a symbol is bound to never changes during a run
   ([step_extends_statics_statement], [run_extends_statics_statement]):
   this is what a rewrite needs, to rely in a handler on a binding made
   before the handler was defined. That the handler of a non-recursive
   continuation with static bindings postdominates its body is left to
   the check here.

   A well-formed unit, run on its own, is never undefined for one of
   these reasons ([well_formed_never_faults_statement]): [static_fault]
   is the three of them, as a test on a state. The proof does not use
   that a handler with static bindings postdominates its body: a
   non-recursive continuation is out of scope in its own handler, which
   is enough for the handler to run once at most.

   The model does not mark exception handlers, so [raises_to] finds them:
   a continuation is one when a call names it as its exception
   continuation.

   The proofs are in FlambdaWellFormedProofs.v, which needs no review. *)

From Stdlib Require Import ZArith List.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaSemanticsSpec.
Import ListNotations.

(* ======================================================================== *)
(* Where control may go                                                     *)
(* ======================================================================== *)

(* The continuations an expression may apply, or give to a call, that it
   does not bind itself. Code is closed, so bindings of code have none. *)
Fixpoint free_continuations (e : expr) : list continuation :=
  match e with
  | Let _ _ body | Let_static _ body => free_continuations body
  | Let_cont_non_recursive k h body =>
    handler_free_continuations h ++ without [k] (free_continuations body)
  | Let_cont_recursive handlers body =>
    without (map fst handlers)
      (flat_map (fun '(_, h) => handler_free_continuations h) handlers
       ++ free_continuations body)
  | Apply ap => [ap_continuation ap; ap_exn_continuation ap]
  | Apply_cont ac => [ac_continuation ac]
  | Switch _ arms => map (fun arm => ac_continuation (snd arm)) arms
  | Invalid => []
  end
with handler_free_continuations (h : continuation_handler)
    : list continuation :=
  match h with
  | Handler _ handler => free_continuations handler
  end.

(* Whether some call in the expression has [k] as its exception
   continuation. *)
Fixpoint raises_to (k : continuation) (e : expr) : bool :=
  match e with
  | Let _ _ body | Let_static _ body => raises_to k body
  | Let_cont_non_recursive _ h body =>
    handler_raises_to k h || raises_to k body
  | Let_cont_recursive handlers body =>
    existsb (fun '(_, h) => handler_raises_to k h) handlers
    || raises_to k body
  | Apply ap => Pos.eqb k (ap_exn_continuation ap)
  | Apply_cont _ | Switch _ _ | Invalid => false
  end
with handler_raises_to (k : continuation) (h : continuation_handler) : bool :=
  match h with
  | Handler _ handler => raises_to k handler
  end.

(* ======================================================================== *)
(* Static bindings are at toplevel                                          *)
(* ======================================================================== *)

(* Whether the handler of the non-recursive continuation [k], bound at
   toplevel around [body], is at toplevel too. *)
Definition handler_at_toplevel (unit_exn k : continuation) (body : expr)
    : bool :=
  negb (raises_to k body)
  && all_among (free_continuations body) [k; unit_exn].

(* CR mshinwell: this refuses a [Let_static] that is not at toplevel even
   when it binds only code. The compiler stops on one that binds a symbol
   and lets one of code alone through (simplify/simplify_named.ml, the case
   [Static_consts]). So the condition is stricter than the compiler, and a
   unit that the compiler builds could fail it; none of the examples does.
   Discrepancy C0-3; no decision yet. *)

(* Every [Let_static] of the expression is at toplevel, given whether the
   expression itself is ([toplevel]) and the exception continuation of the
   unit. *)
Fixpoint statics_at_toplevel (unit_exn : continuation) (toplevel : bool)
    (e : expr) : bool :=
  match e with
  | Let _ _ body => statics_at_toplevel unit_exn toplevel body
  | Let_static bindings body =>
    toplevel
    && forallb (binding_statics_at_toplevel unit_exn) bindings
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_non_recursive k h body =>
    handler_statics_at_toplevel unit_exn
      (toplevel && handler_at_toplevel unit_exn k body) h
    && statics_at_toplevel unit_exn toplevel body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_statics_at_toplevel unit_exn false h)
      handlers
    && statics_at_toplevel unit_exn toplevel body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => true
  end
with handler_statics_at_toplevel (unit_exn : continuation) (toplevel : bool)
    (h : continuation_handler) : bool :=
  match h with
  | Handler _ handler => statics_at_toplevel unit_exn toplevel handler
  end
with binding_statics_at_toplevel (unit_exn : continuation)
    (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ c => code_statics_at_toplevel unit_exn c
  | Bind_deleted_code _ | Bind_symbol _ _ => true
  end
with code_statics_at_toplevel (unit_exn : continuation) (c : code) : bool :=
  match c with
  | Code _ _ _ _ body => statics_at_toplevel unit_exn false body
  end.

(* ======================================================================== *)
(* Static names are bound once                                              *)
(* ======================================================================== *)

Definition code_ids_of_binding (binding : static_binding) : list code_id :=
  match binding with
  | Bind_code id _ => [id]
  | Bind_deleted_code _ | Bind_symbol _ _ => []
  end.

Definition symbols_of_binding (binding : static_binding) : list symbol :=
  match binding with
  | Bind_symbol s _ => [s]
  | Bind_code _ _ | Bind_deleted_code _ => []
  end.

(* The names the [Let_static]s of an expression bind, by [names_of] for
   one binding. Deleted code is not bound, as in the semantics. Code is
   not looked into: in a well-formed unit it binds nothing. *)
Fixpoint static_names (names_of : static_binding -> list positive)
    (e : expr) : list positive :=
  match e with
  | Let _ _ body => static_names names_of body
  | Let_static bindings body =>
    flat_map names_of bindings ++ static_names names_of body
  | Let_cont_non_recursive _ h body =>
    handler_static_names names_of h ++ static_names names_of body
  | Let_cont_recursive handlers body =>
    flat_map (fun '(_, h) => handler_static_names names_of h) handlers
    ++ static_names names_of body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => []
  end
with handler_static_names (names_of : static_binding -> list positive)
    (h : continuation_handler) : list positive :=
  match h with
  | Handler _ handler => static_names names_of handler
  end.

(* ======================================================================== *)
(* Sets of closures are whole                                               *)
(* ======================================================================== *)

(* A closure of a set: the function slots of the set are distinct, the
   closure is at one of them, and the functions of the set have each
   their own code. *)
Definition set_well_formed (slot : function_slot)
    (function_decls : list (function_slot * code_id)) : bool :=
  is_bound slot function_decls
  && distinct (map fst function_decls)
  && distinct (map snd function_decls).

Definition named_sets_well_formed (d : named) : bool :=
  match d with
  | Closure_of_set slot function_decls _ =>
    set_well_formed slot function_decls
  | Simple _ | Prim _ _ | Set_of_closures _ _ | Project_value_slot _ _
  | Project_value_slot_from _ _ _ | Project_function_slot _ _ _ =>
    true
  end.

(* Whether a binding binds the symbol to the constant. *)
Definition binds_symbol_to (s : symbol) (const : static_const)
    (binding : static_binding) : bool :=
  match binding with
  | Bind_symbol s' const' =>
    Pos.eqb s s' && if static_const_eq_dec const const' then true else false
  | Bind_code _ _ | Bind_deleted_code _ => false
  end.

(* A binding of a group which binds a symbol to a closure of a static
   set: the set has a symbol for each of its functions, in their order;
   the symbol bound is the one the set has for the slot; and the group
   binds every symbol of the set to the closure of the same set at that
   symbol's slot. This is what the one pattern of the compiler binds
   ([Bound_static.Pattern.Set_of_closures], against which
   [Static_const.match_against_bound_static_pattern] checks the function
   slots of the set, in order). *)
Definition static_set_whole (bindings : list static_binding)
    (binding : static_binding) : bool :=
  match binding with
  | Bind_symbol s
      (Static_const_closure_of_set slot closure_symbols function_decls
         value_slots) =>
    set_well_formed slot function_decls
    && (if
          list_eq_dec Pos.eq_dec (map fst closure_symbols)
            (map fst function_decls)
        then true
        else false)
    && match lookup slot closure_symbols with
       | Some s' => Pos.eqb s s'
       | None => false
       end
    && forallb
         (fun '(slot', s') =>
            existsb
              (binds_symbol_to s'
                 (Static_const_closure_of_set slot' closure_symbols
                    function_decls value_slots))
              bindings)
         closure_symbols
  | Bind_symbol _
      (Static_const_set_of_closures _ _ | Static_const_block _ _
      | Static_const_boxed_number _ | Static_const_immutable_string _)
  | Bind_code _ _ | Bind_deleted_code _ =>
    true
  end.

(* The code ids of the functions of the static set of which a binding
   binds a closure; none for another binding. *)
Definition static_set_code_ids (binding : static_binding) : list code_id :=
  match binding with
  | Bind_symbol _ (Static_const_set_of_closures code _) => [code]
  | Bind_symbol _ (Static_const_closure_of_set _ _ function_decls _) =>
    map snd function_decls
  | Bind_symbol _
      (Static_const_block _ _ | Static_const_boxed_number _
      | Static_const_immutable_string _)
  | Bind_code _ _ | Bind_deleted_code _ =>
    []
  end.

(* Whether the second binding binds one of the symbols of the static set
   of which the first binds a closure. In a group that binds its sets
   whole, the two are then bindings of one set. *)
Definition binds_symbol_of_set (binding binding' : static_binding) : bool :=
  match binding, binding' with
  | Bind_symbol _ (Static_const_closure_of_set _ closure_symbols _ _),
    Bind_symbol s' _ =>
    among s' (map snd closure_symbols)
  | _, _ => false
  end.

(* The static sets that a group binds have no code in common. A set is
   counted once, though each of its symbols has a binding of its own.
   Simplify gives each code id of the sets of one group one new code id
   (Simplify_set_of_closures_context, the old-to-new code ids of all the
   sets), and fails on a group two of whose sets have the same code.
   Two sets bound by two groups may have the same. *)
Fixpoint static_sets_code_disjoint (bindings : list static_binding) : bool :=
  match bindings with
  | [] => true
  | binding :: bindings =>
    forallb
      (fun binding' =>
         orb (binds_symbol_of_set binding binding')
           match
             inter (static_set_code_ids binding)
               (static_set_code_ids binding')
           with
           | [] => true
           | _ :: _ => false
           end)
      bindings
    && static_sets_code_disjoint bindings
  end.

(* Every closure of a set that the expression makes is at a function slot
   of its set, whose function slots are distinct and whose functions
   have each their own code; every static set is bound whole by the
   group that binds one of its symbols; and the static sets of one group
   have no code in common. Code and handlers are looked into. *)
Fixpoint sets_well_formed (e : expr) : bool :=
  match e with
  | Let _ d body => named_sets_well_formed d && sets_well_formed body
  | Let_static bindings body =>
    forallb (static_set_whole bindings) bindings
    && static_sets_code_disjoint bindings
    && forallb binding_sets_well_formed bindings
    && sets_well_formed body
  | Let_cont_non_recursive _ h body =>
    handler_sets_well_formed h && sets_well_formed body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_sets_well_formed h) handlers
    && sets_well_formed body
  | Apply _ | Apply_cont _ | Switch _ _ | Invalid => true
  end
with handler_sets_well_formed (h : continuation_handler) : bool :=
  match h with
  | Handler _ handler => sets_well_formed handler
  end
with binding_sets_well_formed (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ c => code_sets_well_formed c
  | Bind_deleted_code _ | Bind_symbol _ _ => true
  end
with code_sets_well_formed (c : code) : bool :=
  match c with
  | Code _ _ _ _ body => sets_well_formed body
  end.

(* ======================================================================== *)
(* Numbers are in range                                                     *)
(* ======================================================================== *)

(* The numbers of a term are among those that the compiler's can be.
   - The tag of every block made, by a [Make_block] or statically, and
     the tag that a [Block_load] names, is at least 0 and below 251.
   - Every constant is in the range of its kind, wherever it is: an
     argument, a value slot, a field of a static block, the contents of
     a static boxed number, the scrutinee of a [Switch].
   - The field and the size of a [Block_load] and the discriminants of
     a [Switch] are integers of the target's OCaml, and the bytes of a
     string are bytes.
   FlambdaPrimitiveSpec.v says what the ranges are (the section "Numbers
   in range").

   This is not stricter than the compiler: there each of these numbers
   is of a type whose values are in range ([Tag.Scannable.t],
   [Reg_width_const.t], [Target_ocaml_int.t], [string]), so every term
   it builds passes. The model's numbers are integers, and without the
   check it has terms that the compiler has not: a block with tag 300,
   an int8 that is 200. The machine does not test the tag of a block,
   and the arithmetic has no value on a constant out of range.

   FlambdaRangeSpec.v says what the check gives: in the run of a unit
   that passes, and so of a well-formed unit, every number that a state
   holds is in range. *)

Definition simple_in_range (s : simple) : bool :=
  match s with
  | Const c => const_in_range c
  | Var _ | Symbol _ => true
  end.

Definition value_slots_in_range (value_slots : list (value_slot * simple))
    : bool :=
  forallb (fun slot => simple_in_range (snd slot)) value_slots.

Definition named_in_range (d : named) : bool :=
  match d with
  | Simple s => simple_in_range s
  | Prim p args => prim_in_range p && forallb simple_in_range args
  | Set_of_closures _ value_slots | Closure_of_set _ _ value_slots =>
    value_slots_in_range value_slots
  | Project_value_slot _ closure | Project_value_slot_from _ _ closure
  | Project_function_slot _ _ closure =>
    simple_in_range closure
  end.

Definition static_const_in_range (const : static_const) : bool :=
  match const with
  | Static_const_set_of_closures _ value_slots
  | Static_const_closure_of_set _ _ _ value_slots =>
    value_slots_in_range value_slots
  | Static_const_block tag fields =>
    tag_in_range tag && forallb simple_in_range fields
  | Static_const_boxed_number contents => simple_in_range contents
  | Static_const_immutable_string bytes => forallb byte_in_range bytes
  end.

Definition apply_cont_in_range (ac : apply_cont) : bool :=
  forallb simple_in_range (ac_args ac).

Definition apply_in_range (ap : apply_expr) : bool :=
  simple_in_range (ap_callee ap) && forallb simple_in_range (ap_args ap).

Definition arm_in_range (arm : Z * apply_cont) : bool :=
  ocaml_int_in_range (fst arm) && apply_cont_in_range (snd arm).

(* Every number of the expression is in range. Code and handlers are
   looked into. *)
Fixpoint numbers_in_range (e : expr) : bool :=
  match e with
  | Let _ d body => named_in_range d && numbers_in_range body
  | Let_static bindings body =>
    forallb binding_numbers_in_range bindings && numbers_in_range body
  | Let_cont_non_recursive _ h body =>
    handler_numbers_in_range h && numbers_in_range body
  | Let_cont_recursive handlers body =>
    forallb (fun '(_, h) => handler_numbers_in_range h) handlers
    && numbers_in_range body
  | Apply ap => apply_in_range ap
  | Apply_cont ac => apply_cont_in_range ac
  | Switch scrutinee arms =>
    simple_in_range scrutinee && forallb arm_in_range arms
  | Invalid => true
  end
with handler_numbers_in_range (h : continuation_handler) : bool :=
  match h with
  | Handler _ handler => numbers_in_range handler
  end
with binding_numbers_in_range (binding : static_binding) : bool :=
  match binding with
  | Bind_code _ c => code_numbers_in_range c
  | Bind_deleted_code _ => true
  | Bind_symbol _ const => static_const_in_range const
  end
with code_numbers_in_range (c : code) : bool :=
  match c with
  | Code _ _ _ _ body => numbers_in_range body
  end.

(* ======================================================================== *)
(* Well-formed units                                                        *)
(* ======================================================================== *)

(* A unit, with its exception continuation: its static bindings are at
   toplevel, and bind each code id and each symbol once; its sets of
   closures are whole; its numbers are in range. *)
Definition well_formed_unit (unit_exn : continuation) (e : expr) : bool :=
  statics_at_toplevel unit_exn true e
  && distinct (static_names code_ids_of_binding e)
  && distinct (static_names symbols_of_binding e)
  && sets_well_formed e
  && numbers_in_range e.

(* ======================================================================== *)
(* What is bound stays bound                                                *)
(* ======================================================================== *)

(* Everything the first static environment binds, the second binds to the
   same thing. *)
Definition statics_extend (statics statics' : static_env) : Prop :=
  (∀ (id : code_id) (c : code),
    lookup id (static_code statics) = Some c ->
    lookup id (static_code statics') = Some c)
  ∧ (∀ (s : symbol) (allocated : statically_allocated_value),
      lookup s (static_values statics) = Some allocated ->
      lookup s (static_values statics') = Some allocated).

Definition step_extends_statics_statement : Prop :=
  ∀ s s' : state,
    step s = Step s' ->
    statics_extend (state_statics s) (state_statics s').

Definition run_extends_statics_statement : Prop :=
  ∀ (n : nat) (s s' : state),
    run n s = Step s' ->
    statics_extend (state_statics s) (state_statics s').

(* ======================================================================== *)
(* A well-formed unit does nothing that is forbidden                        *)
(* ======================================================================== *)

Definition code_id_bound (statics : static_env) (id : code_id) : bool :=
  match lookup id (static_code statics) with
  | Some _ => true
  | None => false
  end.

Definition symbol_bound (statics : static_env) (s : symbol) : bool :=
  match lookup s (static_values statics) with
  | Some _ => true
  | None => false
  end.

(* A group binds a name twice, or a name that is bound already. *)
Definition rebinds (names_of : static_binding -> list positive)
    (is_bound : positive -> bool) (bindings : list static_binding) : bool :=
  negb (distinct (flat_map names_of bindings))
  || existsb is_bound (flat_map names_of bindings).

(* The callee is a closure of code whose body binds something static. *)
Definition calls_code_binding_statics (ap : apply_expr) (vars : env)
    (statics : static_env) : bool :=
  match eval_simple vars (ap_callee ap) with
  | Some callee =>
    match closure_of statics callee with
    | Some (called, _) =>
      match lookup called (static_code statics) with
      | Some c => binds_statics (code_body c)
      | None => false
      end
    | None => false
    end
  | None => false
  end.

(* The state is one the machine makes undefined to keep static bindings
   from being executed twice. *)
Definition static_fault (s : state) : bool :=
  match state_expr s with
  | Let_static bindings _ =>
    rebinds code_ids_of_binding (code_id_bound (state_statics s)) bindings
    || rebinds symbols_of_binding (symbol_bound (state_statics s)) bindings
  | Let_cont_recursive handlers _ => handlers_bind_statics handlers
  | Apply ap =>
    calls_code_binding_statics ap (state_vars s) (state_statics s)
  | Let _ _ _ | Let_cont_non_recursive _ _ _ | Apply_cont _ | Switch _ _
  | Invalid =>
    false
  end.

Definition well_formed_never_faults_statement : Prop :=
  ∀ (unit_exn : continuation) (e : expr) (n : nat) (s : state),
    well_formed_unit unit_exn e = true ->
    run n (State e [] [] empty_static_env) = Step s ->
    static_fault s = false.
