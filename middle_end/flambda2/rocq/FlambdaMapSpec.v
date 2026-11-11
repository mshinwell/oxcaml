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

(* Finite maps and sets keyed by names: the one representation of
   environments.

   This file is to be reviewed: the definitions, and the statements at the
   end, which say what each operation does in terms of [lookup] and
   [among]. Whatever maps names to things or collects names, in the
   semantics and in the types alike, is to be built with what is here: a
   file must not define its own lookup, membership test or merge. The
   lemmas are in FlambdaMapProofs.v, which needs no review; a lemma about
   these operations that is not about one construct of the terms belongs
   there, and nowhere else.

   Names. Variables, continuations, symbols, code ids and value slots are
   all [positive] (FlambdaModel.v), so one map and one set serve where the
   compiler has [Variable.Map], [Symbol.Map], [Code_id.Map],
   [Continuation.Map] and [Value_slot.Map], and the sets of each.

   The representation. A map is an association list ([finite_map]) in
   which the first binding of a name is the one that counts ([lookup]). A
   set of names is a list of them, in which a name may occur more than
   once ([among]). The empty map and the empty set are [[]]; to bind a
   name is to cons a pair, which shadows the bindings after it; the union
   of two sets is [++].

   Why lists.
   - The machine of FlambdaSemanticsSpec.v is built of them and every
     statement is written with them: a state's environments, the
     environments its continuation closures keep, and the static
     environment are association lists, extended by cons, which is the
     shadowing of the model's binders. Another representation would mean
     rewriting the machine and every Spec file, or having two.
   - They nest. A continuation closure holds an environment of
     continuation closures, a value holds the values of its slots, and
     types will hold maps of types. An inductive type may recur through
     [list], and functions and proofs over it are structural recursion
     through [map], [forallb] and [flat_map], which Rocq accepts as they
     stand.
   - They extract to OCaml lists and functions over them, with no functor
     and no proof carried in the data, and the conversion from the
     compiler's maps is [bindings].

   What was rejected.
   - Rocq's [FMapPositive] and [FMapAVL] (and the [MSet]s), whose lookups
     are logarithmic. Two maps with the same bindings need not be equal
     there either, so nothing is gained for equality. A proof about a
     type that recurs through one goes by induction on the tree inside
     the map and by the lemmas about [find] and [elements], where with a
     list it is [induction] on the list, as every nested proof here
     already is. The AVL maps are functors and extract as functors. And
     the machine and its proofs would have to be rewritten.
   - Canonical binary tries, in which maps with the same bindings are
     equal. The best for equality and for speed, but the installation
     has no such library (only Rocq's own), so it would have to be
     written and proved here; nesting is as for the trees above; and the
     machine and its proofs would have to be rewritten.
   - Functions [positive -> option A]: no domain to iterate over, nothing
     decidable, nothing to extract.
   - Sorted lists without duplicates, as a subset type: canonical, but to
     bind is no longer to cons, so the environments of closures share
     nothing, and proofs travel with the data.

   What this costs, and how to live with it.
   - [lookup] is linear and [merge] quadratic. The extracted code is for
     tests and differential comparison, not for the compiler.
   - Two maps that bind the same names to the same things need not be
     equal: say [map_equal], not [=], and state what an operation does by
     its [lookup] (as the statements here do), never by the list it
     returns. [compact] gives the bindings that count, one for each name,
     for when a map has to be gone through.
   - Only [lookup] and consing may look at the list. Go through the
     other operations and their lemmas, so that a faster representation
     can be put under them one day without touching their users. *)

From Stdlib Require Import PArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
Import ListNotations.

(* ======================================================================== *)
(* Sets of names                                                            *)
(* ======================================================================== *)

(* [Set.mem]. *)
Definition among (name : positive) (names : list positive) : bool :=
  existsb (Pos.eqb name) names.

(* [Set.subset]. *)
Definition all_among (names allowed : list positive) : bool :=
  forallb (fun name => among name allowed) names.

(* [Set.diff names bound]. *)
Definition without (bound names : list positive) : list positive :=
  filter (fun name => negb (among name bound)) names.

(* [Set.inter]. *)
Definition inter (names names' : list positive) : list positive :=
  filter (fun name => among name names') names.

(* No name occurs twice. *)
Fixpoint distinct (names : list positive) : bool :=
  match names with
  | [] => true
  | name :: names => negb (among name names) && distinct names
  end.

(* The same names, each once: the first occurrence of each is kept. *)
Fixpoint dedup (names : list positive) : list positive :=
  match names with
  | [] => []
  | name :: names => name :: without [name] (dedup names)
  end.

(* Two lists are the same set. *)
Definition same_names (names names' : list positive) : Prop :=
  ∀ name : positive, among name names = among name names'.

(* ======================================================================== *)
(* Maps                                                                     *)
(* ======================================================================== *)

Definition finite_map (A : Type) : Type := list (positive * A).

(* [Map.find_opt]: the first binding of a name. *)
Fixpoint lookup {A : Type} (name : positive) (bindings : list (positive * A))
    : option A :=
  match bindings with
  | [] => None
  | (bound, a) :: bindings =>
    if Pos.eqb name bound then Some a else lookup name bindings
  end.

(* [Map.mem]. *)
Definition is_bound {A : Type} (name : positive) (bindings : finite_map A)
    : bool :=
  match lookup name bindings with
  | Some _ => true
  | None => false
  end.

(* [Map.remove]: every binding of the name goes. *)
Definition unbind {A : Type} (name : positive) (bindings : finite_map A)
    : finite_map A :=
  filter (fun binding => negb (Pos.eqb name (fst binding))) bindings.

(* [Map.map]. *)
Definition map_values {A B : Type} (f : A -> B) (bindings : finite_map A)
    : finite_map B :=
  map (fun binding => (fst binding, f (snd binding))) bindings.

(* [Map.keys]: the names bound, each once, the latest bound first. *)
Definition domain {A : Type} (bindings : finite_map A) : list positive :=
  dedup (map fst bindings).

(* The map that binds each of [names] to what [f] gives for it, if it gives
   something. *)
Definition tabulate {A : Type} (f : positive -> option A)
    (names : list positive) : finite_map A :=
  flat_map
    (fun name =>
       match f name with
       | Some a => [(name, a)]
       | None => []
       end)
    names.

(* [Map.bindings]: the same map with one binding for each name bound, the
   one that counts. *)
Definition compact {A : Type} (bindings : finite_map A) : finite_map A :=
  tabulate (fun name => lookup name bindings) (domain bindings).

(* [Map.filter]. It is the bindings that count that are kept or not: a
   binding that is shadowed never comes back. *)
Definition filter_bindings {A : Type} (keep : positive -> A -> bool)
    (bindings : finite_map A) : finite_map A :=
  tabulate
    (fun name =>
       match lookup name bindings with
       | Some a => if keep name a then Some a else None
       | None => None
       end)
    (domain bindings).

(* [Map.merge], without the key: each name bound by either map is bound to
   what [f] makes of what the two bind it to. [f None None] must be
   [None], as it is not asked. *)
Definition merge {A B C : Type} (f : option A -> option B -> option C)
    (bindings : finite_map A) (bindings' : finite_map B) : finite_map C :=
  tabulate (fun name => f (lookup name bindings) (lookup name bindings'))
    (dedup (map fst bindings ++ map fst bindings')).

(* [Map.union]: the names of either, those of both combined by [f]. This
   is the shape of a meet of environments. *)
Definition union_with {A : Type} (f : A -> A -> A)
    (bindings bindings' : finite_map A) : finite_map A :=
  merge
    (fun a a' =>
       match a, a' with
       | Some a, Some a' => Some (f a a')
       | Some a, None => Some a
       | None, a' => a'
       end)
    bindings bindings'.

(* [Map.inter]: the names of both, combined by [f]. This is the shape of
   a join of environments. *)
Definition inter_with {A B C : Type} (f : A -> B -> C)
    (bindings : finite_map A) (bindings' : finite_map B) : finite_map C :=
  merge
    (fun a b =>
       match a, b with
       | Some a, Some b => Some (f a b)
       | _, _ => None
       end)
    bindings bindings'.

(* Two maps bind the same names to the same things. This, and not [=], is
   when two maps are the same. *)
Definition map_equal {A : Type} (bindings bindings' : finite_map A) : Prop :=
  ∀ name : positive, lookup name bindings = lookup name bindings'.

(* Everything the first map binds, the second binds to the same thing. *)
Definition map_included {A : Type} (bindings bindings' : finite_map A)
    : Prop :=
  ∀ (name : positive) (a : A),
    lookup name bindings = Some a -> lookup name bindings' = Some a.

(* ======================================================================== *)
(* What the operations do                                                   *)
(* ======================================================================== *)

(* Sets. *)

Definition all_among_statement : Prop :=
  ∀ names allowed : list positive,
    all_among names allowed = true
    <-> (∀ name : positive,
          among name names = true -> among name allowed = true).

Definition among_without_statement : Prop :=
  ∀ (name : positive) (bound names : list positive),
    among name (without bound names)
    = among name names && negb (among name bound).

Definition among_inter_statement : Prop :=
  ∀ (name : positive) (names names' : list positive),
    among name (inter names names') = among name names && among name names'.

Definition among_dedup_statement : Prop :=
  ∀ (name : positive) (names : list positive),
    among name (dedup names) = among name names.

Definition dedup_distinct_statement : Prop :=
  ∀ names : list positive, distinct (dedup names) = true.

(* Maps. *)

Definition lookup_unbind_statement : Prop :=
  ∀ (A : Type) (name removed : positive) (bindings : finite_map A),
    lookup name (unbind removed bindings)
    = if Pos.eqb name removed then None else lookup name bindings.

Definition lookup_map_values_statement : Prop :=
  ∀ (A B : Type) (f : A -> B) (name : positive) (bindings : finite_map A),
    lookup name (map_values f bindings) = option_map f (lookup name bindings).

Definition among_domain_statement : Prop :=
  ∀ (A : Type) (name : positive) (bindings : finite_map A),
    among name (domain bindings) = is_bound name bindings.

Definition domain_distinct_statement : Prop :=
  ∀ (A : Type) (bindings : finite_map A), distinct (domain bindings) = true.

Definition lookup_tabulate_statement : Prop :=
  ∀ (A : Type) (f : positive -> option A) (name : positive)
    (names : list positive),
    lookup name (tabulate f names) = if among name names then f name else None.

Definition lookup_compact_statement : Prop :=
  ∀ (A : Type) (name : positive) (bindings : finite_map A),
    lookup name (compact bindings) = lookup name bindings.

Definition compact_distinct_statement : Prop :=
  ∀ (A : Type) (bindings : finite_map A),
    distinct (map fst (compact bindings)) = true.

Definition lookup_filter_bindings_statement : Prop :=
  ∀ (A : Type) (keep : positive -> A -> bool) (name : positive)
    (bindings : finite_map A),
    lookup name (filter_bindings keep bindings)
    = match lookup name bindings with
      | Some a => if keep name a then Some a else None
      | None => None
      end.

Definition lookup_merge_statement : Prop :=
  ∀ (A B C : Type) (f : option A -> option B -> option C) (name : positive)
    (bindings : finite_map A) (bindings' : finite_map B),
    f None None = None ->
    lookup name (merge f bindings bindings')
    = f (lookup name bindings) (lookup name bindings').

Definition lookup_union_with_statement : Prop :=
  ∀ (A : Type) (f : A -> A -> A) (name : positive)
    (bindings bindings' : finite_map A),
    lookup name (union_with f bindings bindings')
    = match lookup name bindings, lookup name bindings' with
      | Some a, Some a' => Some (f a a')
      | Some a, None => Some a
      | None, a' => a'
      end.

Definition lookup_inter_with_statement : Prop :=
  ∀ (A B C : Type) (f : A -> B -> C) (name : positive)
    (bindings : finite_map A) (bindings' : finite_map B),
    lookup name (inter_with f bindings bindings')
    = match lookup name bindings, lookup name bindings' with
      | Some a, Some b => Some (f a b)
      | _, _ => None
      end.
