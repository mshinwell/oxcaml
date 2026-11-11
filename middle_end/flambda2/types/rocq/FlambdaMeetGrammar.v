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



(* What meet uses of the grammar of types and of its neighbours, and
   that FlambdaTypeGrammar.v, FlambdaTypingEnv.v and FlambdaMapSpec.v
   do not have yet.

   This file is to be reviewed, each definition against the function of
   the compiler that it names. It holds definitions only and it
   extracts. Every definition here belongs in another file, which is
   not this stream's to edit: it is to move there, under the same name,
   when its owner takes it, and this file is to go. They are:
   - of middle_end/flambda2/types/grammar/type_grammar.ml and
     kinds/flambda_kind.ml, for FlambdaTypeGrammar.v (T1):
     [naked_number_kind_eqb], [block_shape_eqb], [const_of_naked_number],
     [must_be_singleton],
     [head_of_kind_value_null], [head_of_kind_value_tagged_immediate],
     [set_of_closures_contents_equal], [_subset] and [_union]; and
     [aliases_with_kinds], a traversal of the grammar that the compiler
     has not, which is the n-way join's (another workstream wrote it)
     and which FlambdaMeetSpec.v needs;
   - of types/env/typing_env_level.ml and typing_env.ml, for
     FlambdaTypingEnv.v (T2): [fold_on_defined_vars], [kind_of_simple];
   - for the module of maps, FlambdaMapSpec.v (C0), which is to have
     them as [Keyed.fold2_on], [Keyed.keys_of_both] and
     [Keyed.merge_fold_on], in the forms agreed with C0: [fold2_on],
     [keys_of_both], [merge_fold_on]. [sort_numbers] is a sort of
     integers, which the module of maps has not and is not to have.

   The differences from the compiler:
   - [must_be_singleton]: the outer [None] is the fatal error of the
     compiler ("Immediates case returned wrong kind of constant"). A
     set of numbers is a list here, and has one number if all its
     numbers are the same one ([Keyed.get_singleton]).
   - [fold_on_defined_vars] goes through the binding times in
     increasing order, as [Binding_time.Map.fold] does. The variables
     of one binding time are a set in the compiler, gone through in
     the order of the variables; here they are a list, gone through in
     its order. The levels that meet cuts from an environment have one
     variable for each binding time.
   - [kind_of_simple] is [Simple.kind]. A variable of the compiler
     carries its kind; a variable of the model does not, and its kind
     is that of the type that the environment has for it
     (FlambdaTypingEnv.v). [None] where the environment has none.
   - A set of slots is a list, compared as a set. *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeMeaningBoolSpec FlambdaBindingTime FlambdaEnvAliases
  FlambdaTypingEnv.
Import ListNotations.

(* ======================================================================== *)
(* Of the grammar of types                                                  *)
(* ======================================================================== *)

(* [Flambda_kind.Naked_number_kind.equal]. *)
Definition naked_number_kind_eqb (k k' : naked_number_kind) : bool :=
  kind_eqb (Naked_number k) (Naked_number k').

(* [Flambda_kind.Scannable_block_shape.equal] and
   [Flambda_kind.Block_shape.equal]. *)
Definition scannable_block_shape_eqb (shape shape' : scannable_block_shape)
    : bool :=
  match shape, shape' with
  | Value_only, Value_only => true
  | Mixed_record value_prefix_size flat_suffix,
    Mixed_record value_prefix_size' flat_suffix' =>
    Nat.eqb value_prefix_size value_prefix_size'
    && lists_eqb naked_number_kind_eqb flat_suffix flat_suffix'
  | Value_only, Mixed_record _ _ | Mixed_record _ _, Value_only => false
  end.

Definition block_shape_eqb (shape shape' : block_shape) : bool :=
  match shape, shape' with
  | Scannable shape, Scannable shape' =>
    scannable_block_shape_eqb shape shape'
  | Float_record, Float_record => true
  | Scannable _, Float_record | Float_record, Scannable _ => false
  end.

(* [Reg_width_const.naked_immediate], [naked_float32], ...: the constant
   that a number of a kind is. *)
Definition const_of_naked_number (k : naked_number_kind) (i : Z) : const :=
  match k with
  | Kind_naked_immediate => Naked_immediate i
  | Kind_naked_float32 => Naked_float32 i
  | Kind_naked_float => Naked_float i
  | Kind_naked_int8 => Naked_int8 i
  | Kind_naked_int16 => Naked_int16 i
  | Kind_naked_int32 => Naked_int32 i
  | Kind_naked_int64 => Naked_int64 i
  | Kind_naked_nativeint => Naked_nativeint i
  | Kind_naked_vec128 => Naked_vec128 i
  | Kind_naked_vec256 => Naked_vec256 i
  | Kind_naked_vec512 => Naked_vec512 i
  | Kind_naked_mask => Naked_mask i
  end.

(* [Simple.must_be_const]. *)
Definition simple_must_be_const (s : simple) : option const :=
  match s with
  | Const c => Some c
  | Var _ | Symbol _ => None
  end.

(* [Type_grammar.must_be_singleton]: the constant that a type has for
   only value, if the type shows it. The outer [None] is a fatal error
   of the compiler. *)
Fixpoint must_be_singleton (t : flambda_type) : option (option const) :=
  match t with
  | Type_value ty =>
    match ty with
    | Unknown | Bottom => Some None
    | Ok (Equals simple) => Some (simple_must_be_const simple)
    | Ok
        (No_alias
           (Head_of_kind_value (Ok (Variant _ immediates _ blocks _ _))
              Not_null)) =>
      match blocks with
      | Or_unknown.Unknown => Some None
      | Or_unknown.Known blocks =>
        if negb (row_like_for_blocks_is_bottom blocks)
        then Some None
        else
          match immediates with
          | Or_unknown.Unknown => Some None
          | Or_unknown.Known immediates =>
            match must_be_singleton immediates with
            | None => None
            | Some None => Some None
            | Some (Some (Naked_immediate i)) =>
              Some (Some (Tagged_immediate i))
            | Some (Some (Poison (Naked_number Kind_naked_immediate))) =>
              Some (Some (Poison Value))
            | Some (Some _) => None
            end
          end
      end
    | Ok (No_alias _) => Some None
    end
  | Type_naked_immediate ty =>
    match ty with
    | Unknown | Bottom => Some None
    | Ok (Equals simple) => Some (simple_must_be_const simple)
    | Ok (No_alias head) =>
      match naked_immediates head with
      | Or_unknown.Unknown => Some None
      | Or_unknown.Known numbers =>
        Some (option_map Naked_immediate (Keyed.get_singleton Z.eqb numbers))
      end
    end
  | Type_naked_number k ty =>
    match ty with
    | Unknown | Bottom => Some None
    | Ok (Equals simple) => Some (simple_must_be_const simple)
    | Ok (No_alias numbers) =>
      Some
        (option_map (const_of_naked_number k)
           (Keyed.get_singleton Z.eqb numbers))
    end
  | Type_rec_info _ | Type_region _ => Some None
  end.

(* [Type_grammar.Head_of_kind_value.null]. *)
Definition head_of_kind_value_null : head_of_kind_value :=
  Head_of_kind_value Bottom (Maybe_null None).

(* [Type_grammar.Head_of_kind_value.create_tagged_immediate]. *)
Definition head_of_kind_value_tagged_immediate (imm : Z)
    : head_of_kind_value :=
  Head_of_kind_value
    (Ok
       (Variant None (Or_unknown.Known (this_naked_immediate imm)) None
          (Or_unknown.Known row_like_for_blocks_bottom) No_extensions false))
    Not_null.

(* [Set_of_closures_contents.equal], [subset] and [union]. *)
Definition set_of_closures_contents_equal
    (contents contents' : set_of_closures_contents) : bool :=
  Keyed.same_keys_b Pos.eqb (contents_closures contents)
    (contents_closures contents')
  && Keyed.same_keys_b Pos.eqb (contents_value_slots contents)
       (contents_value_slots contents').

Definition set_of_closures_contents_subset
    (contents contents' : set_of_closures_contents) : bool :=
  all_among (contents_closures contents) (contents_closures contents')
  && all_among (contents_value_slots contents)
       (contents_value_slots contents').

Definition set_of_closures_contents_union
    (contents contents' : set_of_closures_contents)
    : set_of_closures_contents :=
  Set_of_closures_contents
    (dedup (contents_closures contents ++ contents_closures contents'))
    (dedup (contents_value_slots contents ++ contents_value_slots contents')).

(* The aliases of a type, each with the kind at which it stands, and
   the variables that hold the results of [Is_int], [Get_tag] and
   [Is_null], which are naked immediates: what the join of types gives
   the join of [Simple]s, with the kind at which it gives it. The
   recursion is that of [free_variables] (FlambdaTypeGrammar.v). *)
Definition aliases_of_descr {head : Type} (kind : flambda_kind)
    (aliases_of_head : head -> list (simple * flambda_kind))
    (ty : type_descr head) : list (simple * flambda_kind) :=
  match ty with
  | Ok (No_alias head) => aliases_of_head head
  | Ok (Equals s) => [(s, kind)]
  | Unknown | Bottom => []
  end.

Definition aliases_of_relation (x : option variable)
    : list (simple * flambda_kind) :=
  match x with
  | Some x => [(Var x, Naked_number Kind_naked_immediate)]
  | None => []
  end.

(* The two arguments stand for the functions being defined below. *)
Definition aliases_of_block_case
    (aliases_with_kinds : flambda_type -> list (simple * flambda_kind))
    (aliases_of_env_extension : env_extension -> list (simple * flambda_kind))
    (case : row_like_block_case) : list (simple * flambda_kind) :=
  flat_map aliases_with_kinds (case_maps_to case)
  ++ aliases_of_env_extension (case_env_extension case).

Fixpoint aliases_with_kinds (t : flambda_type)
    : list (simple * flambda_kind) :=
  match t with
  | Type_value ty =>
    aliases_of_descr Value aliases_of_head_of_kind_value ty
  | Type_naked_immediate ty =>
    aliases_of_descr (Naked_number Kind_naked_immediate) (fun _ => []) ty
  | Type_naked_number k ty =>
    aliases_of_descr (Naked_number k) (fun _ => []) ty
  | Type_rec_info ty => aliases_of_descr Rec_info (fun _ => []) ty
  | Type_region ty => aliases_of_descr Region (fun _ => []) ty
  end

with aliases_of_head_of_kind_value (head : head_of_kind_value)
    : list (simple * flambda_kind) :=
  match head with
  | Head_of_kind_value non_null is_null =>
    match non_null with
    | Ok head => aliases_of_head_of_kind_value_non_null head
    | Unknown | Bottom => []
    end
    ++ match is_null with
       | Not_null => []
       | Maybe_null is_null => aliases_of_relation is_null
       end
  end

with aliases_of_head_of_kind_value_non_null
    (head : head_of_kind_value_non_null) : list (simple * flambda_kind) :=
  match head with
  | Variant is_int immediates get_tag blocks extensions _ =>
    aliases_of_relation is_int
    ++ match immediates with
       | Or_unknown.Known ty => aliases_with_kinds ty
       | Or_unknown.Unknown => []
       end
    ++ aliases_of_relation get_tag
    ++ match blocks with
       | Or_unknown.Known blocks => aliases_of_row_like_for_blocks blocks
       | Or_unknown.Unknown => []
       end
    ++ match extensions with
       | No_extensions => []
       | Ext when_immediate when_block =>
         aliases_of_env_extension when_immediate
         ++ aliases_of_env_extension when_block
       end
  | Mutable_block _ | String _ => []
  | Boxed_number _ contents _ => aliases_with_kinds contents
  | Closures by_function_slot _ =>
    aliases_of_row_like_for_closures by_function_slot
  end

with aliases_of_row_like_for_blocks (blocks : row_like_for_blocks)
    : list (simple * flambda_kind) :=
  match blocks with
  | Row_like_for_blocks known_tags other_tags _ =>
    flat_map
      (fun case =>
         match snd case with
         | Or_unknown.Known case =>
           aliases_of_block_case aliases_with_kinds aliases_of_env_extension
             case
         | Or_unknown.Unknown => []
         end)
      known_tags
    ++ match other_tags with
       | Or_bottom.Ok case =>
         aliases_of_block_case aliases_with_kinds aliases_of_env_extension
           case
       | Or_bottom.Bottom => []
       end
  end

with aliases_of_row_like_for_closures (closures : row_like_for_closures)
    : list (simple * flambda_kind) :=
  match closures with
  | Row_like_for_closures known_closures =>
    flat_map
      (fun case =>
         aliases_of_closures_entry (case_maps_to (snd case))
         ++ aliases_of_env_extension (case_env_extension (snd case)))
      known_closures
  end

with aliases_of_closures_entry (entry : closures_entry)
    : list (simple * flambda_kind) :=
  match entry with
  | Closures_entry _ closure_types value_slot_types =>
    flat_map (fun binding => aliases_with_kinds (snd binding)) closure_types
    ++ flat_map (fun binding => aliases_with_kinds (snd binding))
         value_slot_types
  end

with aliases_of_env_extension (extension : env_extension)
    : list (simple * flambda_kind) :=
  match extension with
  | Env_extension equations =>
    flat_map (fun binding => aliases_with_kinds (snd binding)) equations
  end.

(* ======================================================================== *)
(* Of the module of maps                                                    *)
(* ======================================================================== *)

(* Integers in increasing order. *)
Fixpoint insert_number (i : Z) (sorted : list Z) : list Z :=
  match sorted with
  | [] => [i]
  | j :: rest => if Z.leb i j then i :: sorted else j :: insert_number i rest
  end.

Definition sort_numbers (numbers : list Z) : list Z :=
  fold_right insert_number [] numbers.

Section Folds.

Context {K : Type}.
Variable eqb : K -> K -> bool.

(* To be [Keyed.fold2_on]: a fold over the keys given, with what each
   of two maps binds a key to. *)
Definition fold2_on {A B S : Type} (keys : list K)
    (f : K -> option A -> option B -> S -> S) (m1 : Keyed.finite_map K A)
    (m2 : Keyed.finite_map K B) (init : S) : S :=
  fold_left
    (fun acc key =>
       f key (Keyed.lookup eqb key m1) (Keyed.lookup eqb key m2) acc)
    keys init.

(* To be [Keyed.keys_of_both]: the keys of both maps, each once, those
   of the first map before those of the second. *)
Definition keys_of_both {A B : Type} (m1 : Keyed.finite_map K A)
    (m2 : Keyed.finite_map K B) : list K :=
  Keyed.dedup eqb (map fst m1 ++ map fst m2).

(* To be [Keyed.merge_fold_on]: the same fold, which also builds the map
   of what [f] answers at each key. *)
Definition merge_fold_on {A B C S : Type} (keys : list K)
    (f : K -> option A -> option B -> S -> option C * S)
    (m1 : Keyed.finite_map K A) (m2 : Keyed.finite_map K B) (init : S)
    : Keyed.finite_map K C * S :=
  fold_left
    (fun (acc : Keyed.finite_map K C * S) key =>
       let '(c, s) :=
         f key (Keyed.lookup eqb key m1) (Keyed.lookup eqb key m2) (snd acc)
       in
       (match c with
        | Some c => fst acc ++ [(key, c)]
        | None => fst acc
        end,
        s))
    keys ([], init).

End Folds.

(* ======================================================================== *)
(* Of the typing environment                                                *)
(* ======================================================================== *)

(* [Typing_env_level.fold_on_defined_vars]: the variables that a level
   defines, with their kinds, in the order of their binding times. A
   variable with no kind in the level, which the compiler would not
   find ([Not_found]), is passed over. *)
Definition fold_on_defined_vars {A : Type}
    (f : variable -> flambda_kind -> A -> A) (level : Typing_env_level.t)
    (init : A) : A :=
  fold_left
    (fun acc binding_time =>
       match
         Keyed.lookup Z.eqb binding_time
           (Typing_env_level.binding_times level)
       with
       | None => acc
       | Some vars =>
         fold_left
           (fun acc var =>
              match lookup var (Typing_env_level.defined_vars level) with
              | Some kind => f var kind acc
              | None => acc
              end)
           vars acc
       end)
    (sort_numbers
       (Keyed.dedup Z.eqb
          (Keyed.domain Z.eqb (Typing_env_level.binding_times level))))
    init.

(* [Simple.kind], read from the environment for a variable. *)
Definition kind_of_simple (tenv : Typing_env.t) (simple : simple)
    : option flambda_kind :=
  match simple with
  | Const c => Some (kind_of_const c)
  | Symbol _ => Some Value
  | Var x => option_map kind (Typing_env.find tenv (Name_var x) None)
  end.
