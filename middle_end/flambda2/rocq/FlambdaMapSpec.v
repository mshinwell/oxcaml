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
   file must not define its own lookup, membership test or merge. (The
   typing environment of today is not built so, and is not a map: see
   the end of this comment.) The lemmas are in FlambdaMapProofs.v, which
   needs no review; a lemma about these operations that is not about one
   construct of the terms belongs there, and nowhere else.

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
     can be put under them one day without touching their users.

   Keys that are not names. The types have maps and sets keyed by tags
   and by numbers, which are integers, and by the names of the types,
   each a variable or a symbol. The module [Keyed], in the second half
   of this file, is for those: it has every definition on names again,
   for keys of any type [K].
   - Each one that compares keys takes the equality test of the keys,
     [eqb : K -> K -> bool], as its first argument, and is otherwise the
     definition on names with [eqb] where that has [Pos.eqb].
     [Keyed.lookup Z.eqb tag cases] is the first case of a tag, and
     [Keyed.inter Z.eqb] the numbers of both of two sets. Those that
     compare no keys take no test: [Keyed.finite_map],
     [Keyed.map_values], [Keyed.tabulate] and [Keyed.is_empty].
   - Use one test for each type of key, named once, with the proof that
     it decides equality: [Pos.eqb] and [Pos.eqb_eq] for names, [Z.eqb]
     and [Z.eqb_eq] for integers, and for another type of key a test
     defined beside the type. The definitions accept any test. The
     statements speak only of one that decides equality; and two such
     tests, though they agree on every pair of keys, are two terms, so
     that a lemma used with one does not apply as it stands to a
     definition written with the other.
   - The statements about [Keyed] are the statements about names, for
     every [K] and every [eqb] that tells whether two keys are the same
     ([decides_equality]), as [Pos.eqb] and [Z.eqb] do. Nothing is
     stated for a test that takes two different keys for the same.
   - The definitions on names stay as they are, under their short
     names, for the machine and all that is written with it. Each is
     the one of [Keyed] at [Pos.eqb], by computation
     ([names_are_keys_statement]), so a lemma about [Keyed] applies to
     them as it stands, and nothing need be proved twice.
   - An operation that is added from now on is added to [Keyed] only.
     Those that go through a map ([Keyed.for_all_bindings],
     [Keyed.at_binding] and their tests) have short names on names;
     these are abbreviations, not definitions.

   Why the test is an argument, and what was rejected.
   - A copy of the definitions and of the statements for integers, and
     another for each type of key to come: as many of everything to
     review, and to keep the same.
   - A functor over the type of the keys, as OCaml's [Map.Make] and
     Rocq's [FMapInterface] are. Each type of key gets a module of its
     own; a statement cannot be about all of them, so each has its own
     copy of the statements to be checked; and the extracted code is
     functors.
   - A type class of keys, so that the test need not be written. Which
     test is used would then be nowhere in the text that uses it; this
     development has no type classes; and the extracted code would pass
     dictionaries.
   - Coding every key as a [positive], as an integer or a name can be,
     and keeping the one type of map. The grammar of types would show
     codes where the compiler has tags and names, every statement would
     be about [lookup (code tag)], and the coding would be one more
     thing to review.
   With the test as an argument, a definition says which equality it
   uses where it is used, [Keyed.lookup] is one function to review
   whatever the keys, and it extracts to an OCaml function that takes
   the test.

   An exception, for now: the typing environment. [typing_env] of
   FlambdaTypesSpec.v (in types/rocq) has the type of a map of types,
   [list (variable * flambda_type)], and is not one. It is a list of
   constraints: [env_satisfies] asks for every pair in the list, not for
   the first pair of each variable, so a variable listed twice has to
   have both types. [[(x, Unknown); (x, Bottom)]] and [[(x, Unknown)]]
   are [map_equal] and mean different things: no environment of values
   satisfies the first, and any that binds [x] satisfies the second. So
   [compact], or putting for a typing environment another that is
   [map_equal] to it, need not preserve [env_satisfies], and what is
   stated here by [lookup] says nothing of what a [typing_env] means.
   When the typing environment is rebuilt on these maps, with one type
   for each variable, what it asks of a variable must still be the
   conjunction of the constraints the list had for it (the meet of its
   types, not the first of them), and the migration has to prove that:
   that [env_satisfies] is preserved. *)

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

(* ======================================================================== *)
(* Keys of any type                                                         *)
(* ======================================================================== *)

(* What is above is keyed by names. What follows is the same for keys of
   any type that has an equality test: see "Keys that are not names" in
   the header. *)

From Stdlib Require Import ZArith.

(* [eqb] tells whether two keys are the same key. A statement below that
   depends on the test assumes this of it. *)
Definition decides_equality {K : Type} (eqb : K -> K -> bool) : Prop :=
  ∀ key key' : K, eqb key key' = true <-> key = key'.

(* [P] holds of every element of a list. This is [Forall] as a function
   that goes through the list, so that Rocq accepts a definition by
   recursion on a type that holds lists or maps of itself, in which [P]
   makes the recursive call. For that, [P] is a parameter of the
   definition and not of its recursion, here and in the definitions
   below that take a predicate or a test. *)
Definition every {A : Type} (P : A -> Prop) : list A -> Prop :=
  fix every (l : list A) : Prop :=
    match l with
    | [] => True
    | a :: l => P a ∧ every l
    end.

(* [every], as a test. *)
Abbreviation every_b := forallb (only parsing).

Module Keyed.

(* [Map.t]: the first binding of a key is the one that counts. *)
Definition finite_map (K A : Type) : Type := list (K * A).

Section Keys.

Context {K : Type} (eqb : K -> K -> bool).

(* Sets of keys. *)

(* [Set.mem]. *)
Definition among (key : K) (keys : list K) : bool :=
  existsb (eqb key) keys.

(* [Set.subset]. *)
Definition all_among (keys allowed : list K) : bool :=
  forallb (fun key => among key allowed) keys.

(* [Set.diff keys removed]. *)
Definition without (removed keys : list K) : list K :=
  filter (fun key => negb (among key removed)) keys.

(* [Set.inter]. *)
Definition inter (keys keys' : list K) : list K :=
  filter (fun key => among key keys') keys.

(* No key occurs twice. *)
Fixpoint distinct (keys : list K) : bool :=
  match keys with
  | [] => true
  | key :: keys => negb (among key keys) && distinct keys
  end.

(* The same keys, each once: the first occurrence of each is kept. *)
Fixpoint dedup (keys : list K) : list K :=
  match keys with
  | [] => []
  | key :: keys => key :: without [key] (dedup keys)
  end.

(* Two lists are the same set. *)
Definition same_keys (keys keys' : list K) : Prop :=
  ∀ key : K, among key keys = among key keys'.

(* [Set.equal]. *)
Definition same_keys_b (keys keys' : list K) : bool :=
  all_among keys keys' && all_among keys' keys.

(* [Set.is_empty] and [Map.is_empty]: the empty set and the empty map are
   [[]], and nothing else is. *)
Definition is_empty {A : Type} (l : list A) : bool :=
  match l with
  | [] => true
  | _ :: _ => false
  end.

(* [Set.get_singleton]: the key of a set that has exactly one. *)
Definition get_singleton (keys : list K) : option K :=
  match dedup keys with
  | [key] => Some key
  | _ => None
  end.

(* Maps. *)

(* [Map.find_opt]: the first binding of a key. *)
Fixpoint lookup {A : Type} (key : K) (bindings : list (K * A)) : option A :=
  match bindings with
  | [] => None
  | (bound, a) :: bindings =>
    if eqb key bound then Some a else lookup key bindings
  end.

(* [Map.mem]. *)
Definition is_bound {A : Type} (key : K) (bindings : finite_map K A)
    : bool :=
  match lookup key bindings with
  | Some _ => true
  | None => false
  end.

(* [Map.remove]: every binding of the key goes. *)
Definition unbind {A : Type} (key : K) (bindings : finite_map K A)
    : finite_map K A :=
  filter (fun binding => negb (eqb key (fst binding))) bindings.

(* [Map.map]. *)
Definition map_values {A B : Type} (f : A -> B) (bindings : finite_map K A)
    : finite_map K B :=
  map (fun binding => (fst binding, f (snd binding))) bindings.

(* [Map.keys]: the keys bound, each once, the latest bound first. *)
Definition domain {A : Type} (bindings : finite_map K A) : list K :=
  dedup (map fst bindings).

(* The map that binds each of [keys] to what [f] gives for it, if it gives
   something. *)
Definition tabulate {A : Type} (f : K -> option A) (keys : list K)
    : finite_map K A :=
  flat_map
    (fun key =>
       match f key with
       | Some a => [(key, a)]
       | None => []
       end)
    keys.

(* [Map.bindings]: the same map with one binding for each key bound, the
   one that counts. *)
Definition compact {A : Type} (bindings : finite_map K A) : finite_map K A :=
  tabulate (fun key => lookup key bindings) (domain bindings).

(* [Map.filter]. It is the bindings that count that are kept or not: a
   binding that is shadowed never comes back. *)
Definition filter_bindings {A : Type} (keep : K -> A -> bool)
    (bindings : finite_map K A) : finite_map K A :=
  tabulate
    (fun key =>
       match lookup key bindings with
       | Some a => if keep key a then Some a else None
       | None => None
       end)
    (domain bindings).

(* [Map.merge], without the key: each key bound by either map is bound to
   what [f] makes of what the two bind it to. [f None None] must be
   [None], as it is not asked. *)
Definition merge {A B C : Type} (f : option A -> option B -> option C)
    (bindings : finite_map K A) (bindings' : finite_map K B)
    : finite_map K C :=
  tabulate (fun key => f (lookup key bindings) (lookup key bindings'))
    (dedup (map fst bindings ++ map fst bindings')).

(* [Map.union]: the keys of either, those of both combined by [f]. *)
Definition union_with {A : Type} (f : A -> A -> A)
    (bindings bindings' : finite_map K A) : finite_map K A :=
  merge
    (fun a a' =>
       match a, a' with
       | Some a, Some a' => Some (f a a')
       | Some a, None => Some a
       | None, a' => a'
       end)
    bindings bindings'.

(* [Map.inter]: the keys of both, combined by [f]. *)
Definition inter_with {A B C : Type} (f : A -> B -> C)
    (bindings : finite_map K A) (bindings' : finite_map K B)
    : finite_map K C :=
  merge
    (fun a b =>
       match a, b with
       | Some a, Some b => Some (f a b)
       | _, _ => None
       end)
    bindings bindings'.

(* Two maps bind the same keys to the same things. This, and not [=], is
   when two maps are the same. *)
Definition map_equal {A : Type} (bindings bindings' : finite_map K A)
    : Prop :=
  ∀ key : K, lookup key bindings = lookup key bindings'.

(* Everything the first map binds, the second binds to the same thing. *)
Definition map_included {A : Type} (bindings bindings' : finite_map K A)
    : Prop :=
  ∀ (key : K) (a : A),
    lookup key bindings = Some a -> lookup key bindings' = Some a.

(* [Map.get_singleton]: the binding of a map that binds exactly one
   key. *)
Definition get_singleton_binding {A : Type} (bindings : finite_map K A)
    : option (K * A) :=
  match compact bindings with
  | [binding] => Some binding
  | _ => None
  end.

(* Going through a map. The four definitions below go through every pair
   of the list that the map is, for the reason given at [every], and ask
   something only of the pairs that [lookup] finds: the bindings that
   count. *)

(* [Map.for_all], as a proposition: [P] holds of every binding. *)
Definition for_all_bindings {A : Type} (P : K -> A -> Prop)
    (bindings : finite_map K A) : Prop :=
  every
    (fun binding =>
       lookup (fst binding) bindings = Some (snd binding)
       -> P (fst binding) (snd binding))
    bindings.

(* [P] holds of what the map binds [key] to, if it binds it. *)
Definition at_binding {A : Type} (P : A -> Prop) (key : K)
    (bindings : finite_map K A) : Prop :=
  every
    (fun binding => lookup key bindings = Some (snd binding) -> P (snd binding))
    bindings.

(* [Map.for_all]: [for_all_bindings], as a test. [seen] is the keys of
   the bindings gone past, which shadow those to come. *)
Definition for_all_bindings_b {A : Type} (p : K -> A -> bool)
    (bindings : finite_map K A) : bool :=
  (fix for_all_bindings_b (seen : list K) (bindings : list (K * A))
       {struct bindings} : bool :=
     match bindings with
     | [] => true
     | (key, a) :: bindings =>
       (among key seen || p key a) && for_all_bindings_b (key :: seen) bindings
     end)
    [] bindings.

(* [at_binding], as a test. *)
Definition at_binding_b {A : Type} (p : A -> bool) (key : K)
    : finite_map K A -> bool :=
  fix at_binding_b (bindings : list (K * A)) : bool :=
    match bindings with
    | [] => true
    | (bound, a) :: bindings =>
      if eqb key bound then p a else at_binding_b bindings
    end.

End Keys.

End Keyed.

(* On names, the four definitions that go through a map have the short
   names that the rest of what is on names has. *)
Abbreviation for_all_bindings := (Keyed.for_all_bindings Pos.eqb).
Abbreviation at_binding := (Keyed.at_binding Pos.eqb).
Abbreviation for_all_bindings_b := (Keyed.for_all_bindings_b Pos.eqb).
Abbreviation at_binding_b := (Keyed.at_binding_b Pos.eqb).

(* ======================================================================== *)
(* What the operations on keys of any type do                               *)
(* ======================================================================== *)

(* The equality tests of names and of integers decide equality. *)

Definition pos_eqb_decides_equality_statement : Prop :=
  decides_equality Pos.eqb.

Definition z_eqb_decides_equality_statement : Prop :=
  decides_equality Z.eqb.

(* Every definition on names of the first half of this file is the one of
   [Keyed] at the equality test of names. *)
Definition names_are_keys_statement : Prop :=
  among = Keyed.among Pos.eqb
  ∧ all_among = Keyed.all_among Pos.eqb
  ∧ without = Keyed.without Pos.eqb
  ∧ inter = Keyed.inter Pos.eqb
  ∧ distinct = Keyed.distinct Pos.eqb
  ∧ dedup = Keyed.dedup Pos.eqb
  ∧ same_names = Keyed.same_keys Pos.eqb
  ∧ finite_map = Keyed.finite_map positive
  ∧ (∀ A : Type, @lookup A = Keyed.lookup Pos.eqb)
  ∧ (∀ A : Type, @is_bound A = Keyed.is_bound Pos.eqb)
  ∧ (∀ A : Type, @unbind A = Keyed.unbind Pos.eqb)
  ∧ (∀ A B : Type, @map_values A B = Keyed.map_values)
  ∧ (∀ A : Type, @domain A = Keyed.domain Pos.eqb)
  ∧ (∀ A : Type, @tabulate A = Keyed.tabulate)
  ∧ (∀ A : Type, @compact A = Keyed.compact Pos.eqb)
  ∧ (∀ A : Type, @filter_bindings A = Keyed.filter_bindings Pos.eqb)
  ∧ (∀ A B C : Type, @merge A B C = Keyed.merge Pos.eqb)
  ∧ (∀ A : Type, @union_with A = Keyed.union_with Pos.eqb)
  ∧ (∀ A B C : Type, @inter_with A B C = Keyed.inter_with Pos.eqb)
  ∧ (∀ A : Type, @map_equal A = Keyed.map_equal Pos.eqb)
  ∧ (∀ A : Type, @map_included A = Keyed.map_included Pos.eqb).

(* Sets. *)

Definition keyed_among_in_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (key : K) (keys : list K), Keyed.among eqb key keys = true <-> key ∈ keys.

(* The union of two sets is [++]. *)
Definition keyed_among_app_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool) (key : K) (keys keys' : list K),
    Keyed.among eqb key (keys ++ keys')
    = Keyed.among eqb key keys || Keyed.among eqb key keys'.

Definition keyed_all_among_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ keys allowed : list K,
      Keyed.all_among eqb keys allowed = true
      <-> (∀ key : K,
            Keyed.among eqb key keys = true
            -> Keyed.among eqb key allowed = true).

Definition keyed_among_without_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (key : K) (removed keys : list K),
      Keyed.among eqb key (Keyed.without eqb removed keys)
      = Keyed.among eqb key keys && negb (Keyed.among eqb key removed).

Definition keyed_among_inter_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (key : K) (keys keys' : list K),
      Keyed.among eqb key (Keyed.inter eqb keys keys')
      = Keyed.among eqb key keys && Keyed.among eqb key keys'.

Definition keyed_among_dedup_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (key : K) (keys : list K),
      Keyed.among eqb key (Keyed.dedup eqb keys) = Keyed.among eqb key keys.

Definition keyed_dedup_distinct_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ keys : list K, Keyed.distinct eqb (Keyed.dedup eqb keys) = true.

Definition keyed_same_keys_b_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ keys keys' : list K,
      Keyed.same_keys_b eqb keys keys' = true
      <-> Keyed.same_keys eqb keys keys'.

Definition keyed_is_empty_among_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ keys : list K,
      Keyed.is_empty keys = true
      <-> (∀ key : K, Keyed.among eqb key keys = false).

(* The set has a singleton when its keys are that one key. *)
Definition keyed_get_singleton_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (key : K) (keys : list K),
      Keyed.get_singleton eqb keys = Some key
      <-> (∀ key' : K, Keyed.among eqb key' keys = eqb key' key).

(* Maps. *)

Definition keyed_lookup_unbind_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (key removed : K) (bindings : Keyed.finite_map K A),
      Keyed.lookup eqb key (Keyed.unbind eqb removed bindings)
      = if eqb key removed then None else Keyed.lookup eqb key bindings.

Definition keyed_lookup_map_values_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool) (A B : Type) (f : A -> B) (key : K)
    (bindings : Keyed.finite_map K A),
    Keyed.lookup eqb key (Keyed.map_values f bindings)
    = option_map f (Keyed.lookup eqb key bindings).

Definition keyed_among_domain_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (key : K) (bindings : Keyed.finite_map K A),
      Keyed.among eqb key (Keyed.domain eqb bindings)
      = Keyed.is_bound eqb key bindings.

Definition keyed_domain_distinct_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (bindings : Keyed.finite_map K A),
      Keyed.distinct eqb (Keyed.domain eqb bindings) = true.

Definition keyed_lookup_tabulate_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (f : K -> option A) (key : K) (keys : list K),
      Keyed.lookup eqb key (Keyed.tabulate f keys)
      = if Keyed.among eqb key keys then f key else None.

Definition keyed_lookup_compact_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (key : K) (bindings : Keyed.finite_map K A),
      Keyed.lookup eqb key (Keyed.compact eqb bindings)
      = Keyed.lookup eqb key bindings.

Definition keyed_compact_distinct_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (bindings : Keyed.finite_map K A),
      Keyed.distinct eqb (map fst (Keyed.compact eqb bindings)) = true.

Definition keyed_lookup_filter_bindings_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (keep : K -> A -> bool) (key : K)
      (bindings : Keyed.finite_map K A),
      Keyed.lookup eqb key (Keyed.filter_bindings eqb keep bindings)
      = match Keyed.lookup eqb key bindings with
        | Some a => if keep key a then Some a else None
        | None => None
        end.

Definition keyed_lookup_merge_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A B C : Type) (f : option A -> option B -> option C) (key : K)
      (bindings : Keyed.finite_map K A) (bindings' : Keyed.finite_map K B),
      f None None = None ->
      Keyed.lookup eqb key (Keyed.merge eqb f bindings bindings')
      = f (Keyed.lookup eqb key bindings) (Keyed.lookup eqb key bindings').

Definition keyed_lookup_union_with_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (f : A -> A -> A) (key : K)
      (bindings bindings' : Keyed.finite_map K A),
      Keyed.lookup eqb key (Keyed.union_with eqb f bindings bindings')
      = match Keyed.lookup eqb key bindings, Keyed.lookup eqb key bindings'
        with
        | Some a, Some a' => Some (f a a')
        | Some a, None => Some a
        | None, a' => a'
        end.

Definition keyed_lookup_inter_with_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A B C : Type) (f : A -> B -> C) (key : K)
      (bindings : Keyed.finite_map K A) (bindings' : Keyed.finite_map K B),
      Keyed.lookup eqb key (Keyed.inter_with eqb f bindings bindings')
      = match Keyed.lookup eqb key bindings, Keyed.lookup eqb key bindings'
        with
        | Some a, Some b => Some (f a b)
        | _, _ => None
        end.

Definition keyed_is_empty_lookup_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (bindings : Keyed.finite_map K A),
      Keyed.is_empty bindings = true
      <-> (∀ key : K, Keyed.lookup eqb key bindings = None).

(* The map has a singleton when it binds that one key, to that. *)
Definition keyed_get_singleton_binding_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (key : K) (a : A) (bindings : Keyed.finite_map K A),
      Keyed.get_singleton_binding eqb bindings = Some (key, a)
      <-> (∀ key' : K,
            Keyed.lookup eqb key' bindings
            = if eqb key' key then Some a else None).

(* Going through a list or a map. *)

Definition every_in_statement : Prop :=
  ∀ (A : Type) (P : A -> Prop) (l : list A),
    every P l <-> (∀ a : A, a ∈ l -> P a).

Definition every_b_every_statement : Prop :=
  ∀ (A : Type) (p : A -> bool) (l : list A),
    every_b p l = true <-> every (fun a => p a = true) l.

Definition keyed_for_all_bindings_lookup_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (P : K -> A -> Prop) (bindings : Keyed.finite_map K A),
      Keyed.for_all_bindings eqb P bindings
      <-> (∀ (key : K) (a : A),
            Keyed.lookup eqb key bindings = Some a -> P key a).

Definition keyed_at_binding_lookup_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool) (A : Type) (P : A -> Prop) (key : K)
    (bindings : Keyed.finite_map K A),
    Keyed.at_binding eqb P key bindings
    <-> (∀ a : A, Keyed.lookup eqb key bindings = Some a -> P a).

Definition keyed_for_all_bindings_b_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool),
    decides_equality eqb ->
    ∀ (A : Type) (p : K -> A -> bool) (bindings : Keyed.finite_map K A),
      Keyed.for_all_bindings_b eqb p bindings = true
      <-> Keyed.for_all_bindings eqb (fun key a => p key a = true) bindings.

Definition keyed_at_binding_b_statement : Prop :=
  ∀ (K : Type) (eqb : K -> K -> bool) (A : Type) (p : A -> bool) (key : K)
    (bindings : Keyed.finite_map K A),
    Keyed.at_binding_b eqb p key bindings = true
    <-> Keyed.at_binding eqb (fun a => p a = true) key bindings.

(* The same two on names, as they are written. *)

Definition for_all_bindings_lookup_statement : Prop :=
  ∀ (A : Type) (P : positive -> A -> Prop) (m : finite_map A),
    for_all_bindings P m
    <-> (∀ (name : positive) (a : A), lookup name m = Some a -> P name a).

Definition at_binding_lookup_statement : Prop :=
  ∀ (A : Type) (P : A -> Prop) (name : positive) (m : finite_map A),
    at_binding P name m <-> (∀ a : A, lookup name m = Some a -> P a).
