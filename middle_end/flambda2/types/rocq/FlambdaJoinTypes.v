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


(* The n-way join of types: the functions of
   middle_end/flambda2/types/meet_and_n_way_join.ml that join.

   This file is to be reviewed line by line against that file. It holds
   definitions only. What they are proved to guarantee is
   FlambdaJoinTypesSpec.v, against the interface with the join of
   environments that FlambdaJoinSpec.v fixes.

   The compiler that is transcribed is the one with the change that
   repairs [n_way_join_closures_entry]: the merge of the function types
   answers [None] unless both sides have a function type. The
   integration branch has taken that change; a tree that has not it yet
   has, in that merge, the cases [None, Some val2] and [Some _, None]
   that [gather_function_types_before_fix] has here. Lines are those of
   the file before the change, which moves nothing above line 2920.

   This is the second part of the transcription: the functions that
   join heads with no types inside them. The others are to come, and
   the header will then say of each of the thirty what the model has.

   How the compiler's functions are written here.
   - The state of the join of environments ([Join_env.t]) is any type:
     the functions are in a section whose variables are that type, the
     four functions of join_env.ml that the traversal calls
     ([Join_env.joined_env], [n_way_join_simples], [import_type] and
     [n_way_join_env_extension], the last under the name
     [join_env_n_way_join_env_extension], this file having a function
     of the same name as the compiler has), and three functions of
     other files: [Expand_head.expand_head],
     [reduce_head_of_kind_naked_immediate] (it is in
     meet_and_n_way_join.ml, with the meet) and the test of structural
     equality of types that the compiler makes under
     -flambda2-join-sharing structural ([Type_grammar.equal]).
   - A function that joins answers a ['a n_way_join_result], a pair of
     an ['a Or_unknown.t] and the state; here it answers an option of
     that, [None] being a fatal error of the compiler, an
     [assert false] or an exception that nothing catches. The header of
     each function says which. An exception that the compiler raises to
     leave a fold and catches a few lines below ([Unknown_result],
     [Cannot_track], [No_extensions]) is an inner [None] of a function
     that gathers a list, and is said so there.
   - [Join_env.machine_width] is not there: a number of the model is an
     integer whatever the machine (FlambdaModel.v).
   - A set of numbers is a list (FlambdaTypeGrammar.v); the union of
     two is their concatenation without repeats.

   What is here, in the order of the compiler's file.
   - [map_join_result] (line 49), [join_alloc_mode] (768),
     [n_way_join_unknown] (790),
     [n_way_join_head_of_kind_naked_number] (803), [deduce_is_int] and
     [deduce_is_int_simple] (867), [deduce_get_tag] and
     [deduce_get_tag_simple] (880), [n_way_join_relation_simples]
     (903): in full.
   - [n_way_join_is_null]: the first binding of
     [n_way_join_head_of_kind_value] (2112 to 2145), which joins the
     variables that say whether the value is null. The compiler stops
     if the join of the [Simple]s answers a symbol.
   - [n_way_join_head_of_kind_naked_immediate] (2588): in full. The
     inverse relations of the heads are dropped, as in the compiler;
     the join of environments rebuilds them. Each head is first reduced
     in the environment of its index. If every head reduces to bottom
     the compiler stops, in [create_naked_immediates_non_empty], and
     the answer here is [None].
   - [n_way_join_head_of_kind_naked_numbers]: the eleven functions
     [n_way_join_head_of_kind_naked_float32] to
     [n_way_join_head_of_kind_naked_mask] (2619 to 2661), which differ
     only in the kind.
   - [n_way_join_head_of_kind_rec_info] (2663): the head of the model
     has no content (FlambdaTypeGrammar.v), so the answer is always
     known. The compiler answers unknown if the expressions differ. So
     the compiler's answer may be unknown where the model's is known,
     never the reverse.
   - [n_way_join_head_of_kind_region] (2668): in full.
   - [n_way_join_env_extension] (3133): in full. The compiler's
     function gives the environment's the join of types and the meet;
     the environment's uses neither (FlambdaJoinSpec.v).
   - [n_way_join_function_type] (3098): a function type of the model
     has no [rec_info] (FlambdaTypeGrammar.v), so the join of the
     [rec_info]s is not there, nor the state, which only that join
     threads. A consequence for the differential tests: where every
     function type is known and all name one code, the model answers
     that code; the compiler answers unknown instead if the join of the
     [rec_info]s is unknown (their heads differ). So the compiler's
     answer may be unknown where the model's is known, never the
     reverse, and never a different code. With invariant checks the
     compiler stops on an empty list; without them it answers unknown,
     as here.
   - [n_way_join_function_types]: of [n_way_join_closures_entry]
     (2895), the part that joins the function types of the entries. A
     function slot is kept only if every entry has a function type for
     it, as [n_way_join_generic_product] does for the closures and the
     value slots, and as the binary join does ([join_closures_entry]
     in meet_and_join.ml).
   - [n_way_join_function_types_before_fix]: the same part as it was
     before the change. For each function slot that some entry has a
     function type for, it joins the function types of the entries that
     have one. An entry that has none for the slot is left out of that
     join: it is not taken to say that the code is unknown. It is not
     an upper bound (FlambdaJoinSpec.v), and is kept only as the record
     of that; nothing else is to use it.

   The lists of contributors are in the order in which the compiler
   makes them (a fold from the left that conses reverses its list);
   no statement depends on the order.

   Stand-ins. Two things that this file needs are another workstream's
   and are not yet where this file can import them. Each is copied
   here under its owner's names, in a module of its own, and is to go,
   with a change of the imports and nothing else, when the owner's
   file is there:
   - [Expanded_type]: the type of expanded types and its creation
     functions, of the file of [Expand_head] (the workstream on meet);
   - [Keyed_fold]: the fold over the bindings of a map that threads a
     state and may drop bindings, which is to be in the module [Keyed]
     of FlambdaMapSpec.v under the same names. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaTypingEnv FlambdaJoinEnv.
Import ListNotations.

(* ======================================================================== *)
(* Stand-ins                                                                *)
(* ======================================================================== *)

(* [Expand_head.Expanded_type]: a type that is not an alias, given by
   its kind and its head. A copy of what this file uses of the module
   of that name in the file of [Expand_head]. *)
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

  Definition create_value (head : head_of_kind_value) : t :=
    create Value (Ok (Head_value head)).

  Definition create_naked_immediate (head : head_of_kind_naked_immediate)
      : t :=
    create (Naked_number Kind_naked_immediate) (Ok (Head_naked_immediate head)).

  (* [create_naked_float32], [create_naked_float], ..., [create_naked_mask]. *)
  Definition create_naked_number (k : naked_number_kind) (head : list Z) : t :=
    create (Naked_number k) (Ok (Head_naked_number k head)).

  Definition create_rec_info (head : unit) : t :=
    create Rec_info (Ok (Head_rec_info head)).

  Definition create_region (head : unit) : t :=
    create Region (Ok (Head_region head)).

  Definition unknown_like (expanded : t) : t :=
    create_unknown (kind expanded).

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

End Expanded_type.

(* To be in the module [Keyed] of FlambdaMapSpec.v, under these names
   and with the equality test of the keys as first argument: a fold
   over keys, or over the bindings of a map, that threads a state,
   builds the map of what the function answers, drops a key for which
   it answers no value, and stops if it fails. *)
Module Keyed_fold.

Section Keys.

Context {K : Type} (eqb : K -> K -> bool).

Fixpoint tabulate_fold_opt {A S : Type}
    (f : K -> S -> option (option A * S)) (keys : list K) (s : S)
    : option (Keyed.finite_map K A * S) :=
  match keys with
  | [] => Some ([], s)
  | key :: keys =>
    match f key s with
    | None => None
    | Some (a, s) =>
      match tabulate_fold_opt f keys s with
      | None => None
      | Some (bindings, s) =>
        Some
          (match a with
           | Some a => (key, a) :: bindings
           | None => bindings
           end,
           s)
      end
    end
  end.

Definition filter_map_fold_on {A B S : Type} (keys : list K)
    (f : K -> A -> S -> option (option B * S))
    (bindings : Keyed.finite_map K A) (s : S)
    : option (Keyed.finite_map K B * S) :=
  tabulate_fold_opt
    (fun key s =>
       match Keyed.lookup eqb key bindings with
       | Some a => f key a s
       | None => Some (None, s)
       end)
    keys s.

(* [Map.filter_map] with a state: each key that the map binds is
   visited once, with what [lookup] finds for it. *)
Definition filter_map_fold {A B S : Type}
    (f : K -> A -> S -> option (option B * S))
    (bindings : Keyed.finite_map K A) (s : S)
    : option (Keyed.finite_map K B * S) :=
  filter_map_fold_on (Keyed.domain eqb bindings) f bindings s.

End Keys.

End Keyed_fold.

(* ======================================================================== *)
(* Function types                                                           *)
(* ======================================================================== *)

(* The function types of a list, if none is unknown. *)
Fixpoint known_function_types
    (func_types : list (Index.t * Or_unknown.t function_type))
    : option (list function_type) :=
  match func_types with
  | [] => Some []
  | (_, Or_unknown.Unknown) :: _ => None
  | (_, Or_unknown.Known func_type) :: func_types =>
    match known_function_types func_types with
    | None => None
    | Some known => Some (func_type :: known)
    end
  end.

(* [n_way_join_function_type]: the code is known if every function type
   is known and all name the same code. *)
Definition n_way_join_function_type
    (func_types : list (Index.t * Or_unknown.t function_type))
    : Or_unknown.t function_type :=
  match known_function_types func_types with
  | None | Some [] => Or_unknown.Unknown
  | Some (func_type :: func_types) =>
    if forallb
         (fun func_type' =>
            Pos.eqb (function_type_code_id func_type)
              (function_type_code_id func_type'))
         func_types
    then Or_unknown.Known func_type
    else Or_unknown.Unknown
  end.

(* The function types of the entries, slot by slot, as
   [n_way_join_closures_entry] gathers them: a slot is kept only if
   every entry has a function type for it. *)
Definition gather_function_types
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (list (Index.t * Or_unknown.t function_type)) :=
  match entries with
  | [] => []
  | (id1, function_types1) :: entries =>
    fold_left
      (fun function_types entry =>
         merge
           (fun vals_opt val2_opt =>
              match vals_opt, val2_opt with
              | None, _ | _, None => None
              | Some vals, Some val2 => Some ((fst entry, val2) :: vals)
              end)
           function_types (snd entry))
      entries
      (map_values (fun func_type => [(id1, func_type)]) function_types1)
  end.

Definition n_way_join_function_types
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (Or_unknown.t function_type) :=
  map_values n_way_join_function_type (gather_function_types entries).

(* The same before the change: the entries that have no function type
   for a slot are not among its contributors, and the slot is kept. *)
Definition gather_function_types_before_fix
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (list (Index.t * Or_unknown.t function_type)) :=
  match entries with
  | [] => []
  | (id1, function_types1) :: entries =>
    fold_left
      (fun function_types entry =>
         merge
           (fun vals_opt val2_opt =>
              match vals_opt, val2_opt with
              | None, None => None
              | None, Some val2 => Some [(fst entry, val2)]
              | Some vals, None => Some vals
              | Some vals, Some val2 => Some ((fst entry, val2) :: vals)
              end)
           function_types (snd entry))
      entries
      (map_values (fun func_type => [(id1, func_type)]) function_types1)
  end.

Definition n_way_join_function_types_before_fix
    (entries : list (Index.t * finite_map (Or_unknown.t function_type)))
    : finite_map (Or_unknown.t function_type) :=
  map_values n_way_join_function_type
    (gather_function_types_before_fix entries).

(* ======================================================================== *)
(* What the traversal is made with                                          *)
(* ======================================================================== *)

(* [Or_unknown.map]. *)
Definition or_unknown_map {A B : Type} (f : A -> B) (a : Or_unknown.t A)
    : Or_unknown.t B :=
  match a with
  | Or_unknown.Known a => Or_unknown.Known (f a)
  | Or_unknown.Unknown => Or_unknown.Unknown
  end.

(* [join_alloc_mode]. *)
Definition join_alloc_mode (alloc_mode1 alloc_mode2 : Alloc_mode.t)
    : Alloc_mode.t :=
  match alloc_mode1, alloc_mode2 with
  | (Alloc_mode.Heap_or_local | Alloc_mode.Local), _
  | _, (Alloc_mode.Heap_or_local | Alloc_mode.Local) =>
    Alloc_mode.Heap_or_local
  | Alloc_mode.Heap, Alloc_mode.Heap => Alloc_mode.Heap
  end.

(* The union of two sets of numbers. *)
Definition numbers_union (numbers numbers' : list Z) : list Z :=
  Keyed.dedup Z.eqb (numbers ++ numbers').

(* [Simple.untagged_const_bool] and [Simple.untagged_const_int] of a
   tag. *)
Definition untagged_const_bool (b : bool) : simple :=
  Const (Naked_immediate (if b then 1%Z else 0%Z)).

Definition untagged_const_int (i : Z) : simple := Const (Naked_immediate i).

(* [Type_grammar.Row_like_for_blocks.all_tags]. *)
Definition row_like_for_blocks_all_tags (blocks : row_like_for_blocks)
    : Or_unknown.t (list Z) :=
  match blocks with
  | Row_like_for_blocks known_tags other_tags _ =>
    match other_tags with
    | Or_bottom.Ok _ => Or_unknown.Unknown
    | Or_bottom.Bottom => Or_unknown.Known (Keyed.domain Z.eqb known_tags)
    end
  end.

(* [deduce_is_int]: whether a variant is an immediate, where its blocks
   or its immediates show that it has none of the one sort. *)
Definition deduce_is_int (blocks : Or_unknown.t row_like_for_blocks)
    (imms : Or_unknown.t flambda_type) : Or_unknown.t bool :=
  let no_blocks :=
    match blocks with
    | Or_unknown.Known blocks => row_like_for_blocks_is_bottom blocks
    | Or_unknown.Unknown => false
    end
  in
  let no_immediates :=
    match imms with
    | Or_unknown.Known imms => is_obviously_bottom imms
    | Or_unknown.Unknown => false
    end
  in
  if no_blocks
  then Or_unknown.Known true
  else if no_immediates then Or_unknown.Known false else Or_unknown.Unknown.

(* [deduce_is_int_simple]. *)
Definition deduce_is_int_simple (blocks : Or_unknown.t row_like_for_blocks)
    (imms : Or_unknown.t flambda_type) (is_int_var : option variable)
    : option simple :=
  match deduce_is_int blocks imms, is_int_var with
  | Or_unknown.Known is_int, _ => Some (untagged_const_bool is_int)
  | Or_unknown.Unknown, Some var => Some (Var var)
  | Or_unknown.Unknown, None => None
  end.

(* [deduce_get_tag]: the tag of the blocks of a variant, if they all
   have one tag; bottom if there is no block. *)
Definition deduce_get_tag (blocks : Or_unknown.t row_like_for_blocks)
    : or_unknown_or_bottom Z :=
  match blocks with
  | Or_unknown.Unknown => Unknown
  | Or_unknown.Known blocks =>
    match row_like_for_blocks_all_tags blocks with
    | Or_unknown.Unknown => Unknown
    | Or_unknown.Known all_tags =>
      if Keyed.is_empty all_tags
      then Bottom
      else
        match Keyed.get_singleton Z.eqb all_tags with
        | Some tag => Ok tag
        | None => Unknown
        end
    end
  end.

(* [deduce_get_tag_simple]. *)
Definition deduce_get_tag_simple (blocks : Or_unknown.t row_like_for_blocks)
    (get_tag_var : option variable) : or_unknown_or_bottom simple :=
  match deduce_get_tag blocks, get_tag_var with
  | Ok get_tag, _ => Ok (untagged_const_int get_tag)
  | Bottom, _ => Bottom
  | Unknown, Some var => Ok (Var var)
  | Unknown, None => Unknown
  end.

(* The contents of a list, if none is unknown, the last first: the fold
   of [n_way_join_unknown]. [None] is its exception [Unknown_result]. *)
Fixpoint known_contents {A : Type} (acc : list (Index.t * A))
    (or_unknowns : list (Index.t * Or_unknown.t A))
    : option (list (Index.t * A)) :=
  match or_unknowns with
  | [] => Some acc
  | (id, Or_unknown.Known contents) :: or_unknowns =>
    known_contents ((id, contents) :: acc) or_unknowns
  | (_, Or_unknown.Unknown) :: _ => None
  end.

(* The [Simple]s that say whether the values of each head are null: the
   [List.map] of [n_way_join_head_of_kind_value]. [None] is its
   exception [Cannot_track]: a head that may be null has no variable
   that says whether it is. *)
Fixpoint is_null_simples (heads : list (Index.t * head_of_kind_value))
    : option (list (Index.t * simple)) :=
  match heads with
  | [] => Some []
  | (id, Head_of_kind_value _ is_null) :: heads =>
    match is_null with
    | Not_null =>
      option_map (cons (id, untagged_const_bool false)) (is_null_simples heads)
    | Maybe_null None => None
    | Maybe_null (Some is_null) =>
      option_map (cons (id, Var is_null)) (is_null_simples heads)
    end
  end.

(* ======================================================================== *)
(* The traversal                                                            *)
(* ======================================================================== *)

Section Traversal.

(* The state of the join of environments, and the functions of
   join_env.ml that the traversal calls. *)
Context {state : Type}
  (joined_env : state -> Index.t -> option Typing_env.t)
  (n_way_join_simples :
     state -> flambda_kind -> list (Index.t * simple)
     -> option (Or_bottom.t simple * state))
  (import_type : state -> flambda_type -> option state)
  (join_env_n_way_join_env_extension :
     state -> list (Index.t * env_extension)
     -> option (Or_bottom.t (env_extension * state))).

(* [Expand_head.expand_head], [reduce_head_of_kind_naked_immediate] and
   [Type_grammar.equal]. *)
Context
  (expand_head : Typing_env.t -> flambda_type -> option Expanded_type.t)
  (reduce_head_of_kind_naked_immediate :
     Typing_env.t -> head_of_kind_naked_immediate
     -> Or_bottom.t head_of_kind_naked_immediate)
  (type_eqb : flambda_type -> flambda_type -> bool).

(* ['a n_way_join_result], or [None] where the compiler stops. *)
Definition n_way_join_result (A : Type) : Type :=
  option (Or_unknown.t A * state).

(* [map_join_result], which [let>>+] is. *)
Definition map_join_result {A B : Type} (f : A -> B)
    (result : n_way_join_result A) : n_way_join_result B :=
  let* '(v, env) := result in
  Some (or_unknown_map f v, env).

(* [n_way_join_unknown]: the join of things each of which may be
   unknown is unknown if one is. *)
Definition n_way_join_unknown {A B : Type}
    (n_way_join_contents : state -> list (Index.t * A) -> n_way_join_result B)
    (env : state) (or_unknowns : list (Index.t * Or_unknown.t A))
    : n_way_join_result B :=
  match known_contents [] or_unknowns with
  | Some contents => n_way_join_contents env contents
  | None => Some (Or_unknown.Unknown, env)
  end.

(* [n_way_join_head_of_kind_naked_number]: the union of the sets. *)
Definition n_way_join_head_of_kind_naked_number (env : state)
    (t1 : list Z * Index.t) (ts : list (Index.t * list Z))
    : n_way_join_result (list Z) :=
  Some
    (Or_unknown.Known
       (fold_left (fun t1 t2 => numbers_union t1 (snd t2)) ts (fst t1)),
     env).

(* [n_way_join_relation_simples]: the variable that holds, in the
   target, what the [Simple]s given hold in the environments joined, if
   the join of the [Simple]s answers a variable. *)
Definition n_way_join_relation_simples (env : state)
    (simples_opt : option (list (Index.t * simple)))
    : option (option variable * state) :=
  match simples_opt with
  | None => Some (None, env)
  | Some simples =>
    let* '(joined, env) :=
      n_way_join_simples env (Naked_number Kind_naked_immediate) simples
    in
    match joined with
    | Or_bottom.Bottom => Some (None, env)
    | Or_bottom.Ok (Const _) => Some (None, env)
    | Or_bottom.Ok (Symbol _) => Some (None, env)
    | Or_bottom.Ok (Var var) => Some (Some var, env)
    end
  end.

(* The first binding of [n_way_join_head_of_kind_value]: whether the
   joined head may be null, and the variable that says whether it is.
   [None] is the fatal error of the compiler for a symbol. *)
Definition n_way_join_is_null (env : state)
    (heads : list (Index.t * head_of_kind_value)) : option (is_null * state) :=
  match is_null_simples heads with
  | None => Some (Maybe_null None, env)
  | Some is_null_simples =>
    let* '(joined, env) :=
      n_way_join_simples env (Naked_number Kind_naked_immediate)
        is_null_simples
    in
    match joined with
    | Or_bottom.Bottom => Some (Maybe_null None, env)
    | Or_bottom.Ok (Const (Naked_immediate i)) =>
      Some (if Z.eqb i 0 then Not_null else Maybe_null None, env)
    | Or_bottom.Ok (Const _) => Some (Maybe_null None, env)
    | Or_bottom.Ok (Symbol _) => None
    | Or_bottom.Ok (Var var) => Some (Maybe_null (Some var), env)
    end
  end.

(* The fold of [n_way_join_head_of_kind_naked_immediate]: the union of
   the numbers of the heads, each reduced in the environment of its
   index; a head that reduces to bottom is left out. [None] is the
   fatal error of [Join_env.joined_env] for an index that it has
   not. *)
Fixpoint join_naked_immediates (env : state)
    (immediates : Or_unknown.t (list Z))
    (heads : list (Index.t * head_of_kind_naked_immediate))
    : option (Or_unknown.t (list Z)) :=
  match heads with
  | [] => Some immediates
  | (id2, head2) :: heads =>
    let* tenv := joined_env env id2 in
    match reduce_head_of_kind_naked_immediate tenv head2 with
    | Or_bottom.Bottom => join_naked_immediates env immediates heads
    | Or_bottom.Ok head2 =>
      let immediates :=
        match immediates, naked_immediates head2 with
        | Or_unknown.Unknown, _ | _, Or_unknown.Unknown => Or_unknown.Unknown
        | Or_unknown.Known imms, Or_unknown.Known imms2 =>
          Or_unknown.Known (numbers_union imms imms2)
        end
      in
      join_naked_immediates env immediates heads
    end
  end.

(* [n_way_join_head_of_kind_naked_immediate]. [None] is also the fatal
   error of [create_naked_immediates_non_empty] for the empty set. *)
Definition n_way_join_head_of_kind_naked_immediate (env : state)
    (heads : list (Index.t * head_of_kind_naked_immediate))
    : n_way_join_result head_of_kind_naked_immediate :=
  let* immediates :=
    join_naked_immediates env (Or_unknown.Known []) heads
  in
  match immediates with
  | Or_unknown.Unknown => Some (Or_unknown.Unknown, env)
  | Or_unknown.Known imms =>
    if Keyed.is_empty imms
    then None
    else
      Some
        (Or_unknown.Known
           (Head_of_kind_naked_immediate (Or_unknown.Known imms) []),
         env)
  end.

(* [n_way_join_head_of_kind_naked_float32], ...,
   [n_way_join_head_of_kind_naked_mask]. *)
Definition n_way_join_head_of_kind_naked_numbers (env : state)
    (t1 : list Z * Index.t) (ts : list (Index.t * list Z))
    : n_way_join_result (list Z) :=
  n_way_join_head_of_kind_naked_number env t1 ts.

(* [n_way_join_head_of_kind_rec_info]. *)
Definition n_way_join_head_of_kind_rec_info (env : state)
    (t1 : unit * Index.t) (ts : list (Index.t * unit))
    : n_way_join_result unit :=
  Some (Or_unknown.Known (fst t1), env).

(* [n_way_join_head_of_kind_region]. *)
Definition n_way_join_head_of_kind_region (env : state)
    (t1 : unit * Index.t) (ts : list (Index.t * unit))
    : n_way_join_result unit :=
  Some (Or_unknown.Known tt, env).

(* [n_way_join_env_extension]: the join of the environment side, with
   the empty extension where it answers bottom. *)
Definition n_way_join_env_extension (env : state)
    (exts : list (Index.t * env_extension)) : option (env_extension * state) :=
  let* joined := join_env_n_way_join_env_extension env exts in
  match joined with
  | Or_bottom.Bottom => Some (empty_env_extension, env)
  | Or_bottom.Ok (ext, env) => Some (ext, env)
  end.

End Traversal.
