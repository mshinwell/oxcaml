# N2: the freshness quantifier. Answer, survey and recommendation

Branch `flambda2-rocq/N2-fresh-quantifier`, in new files only, on the
integration branch after C2's epoch and N1's step 3b (in which the
renaming enters code) with the statements on the classes that follow
it. The question was the human's: can the
quantifier of the papers on nominal sets be used here, the reversed N
that reads "for all but finitely many names"; would it make statements
easier; and it would be good to have.

Contents: 1 the answer in one page, with three statements before and
after; 2 what is in the files; 3 the notation and the tools; 4 the
survey, statement by statement; 5 what it would cost to make it the
primary form; 6 what it gives the proofs still to come; 7 before and
after, more; 8 what is not done; 9 the statements written with the
older accounts of free names.

## 1. The answer

### Three statements, before and after

**Equality of name abstractions.** As it stands (N1's definition, for
any bindable):

    ∃ p p' : permutation,
      opens p a ∧ opens p' a'
      ∧ fst (pattern_match p a) = fst (pattern_match p' a')
      ∧ equal NT (snd (pattern_match p a)) (snd (pattern_match p' a'))

With the quantifier, proved to be the same relation for one bound
name (`equal_abstraction_fresh`), `concretion NT a c` being the scope
of `a` with its bound name exchanged for `c`:

    И c, equal NT (concretion NT a c) (concretion NT a' c)

**A function defined through `pattern_match` is well defined.** As it
stands (N1's `pattern_match_well_defined`, its last premises and its
conclusion):

    (∀ (ab : B * T) (name : positive),
      among name (free_names NB (fst ab)) = true ->
      among name (free_names NX (f ab)) = false) ->
    equal_abstraction NB NT a a' ->
    opens NB NT p a ->
    opens NB NT p' a' ->
    equal NX (f (pattern_match NB NT p a)) (f (pattern_match NB NT p' a'))

With the quantifier, for one bound name, proved from the statement
above (`concretion_well_defined`):

    (И name, ∀ t : T, among name (free_names NX (f (name, t))) = false) ->
    equal_abstraction single_name NT a a' ->
    И c c', equal NX (f (c, concretion NT a c)) (f (c', concretion NT a' c'))

**A function that makes fresh names does not depend on them** (the
equivariance of the join). As T5 and N1 agreed it in words, written
out for a function `g` that is given the names it is to use: for two
lists of fresh names,

    ∃ p : permutation,
      fixes p (free_names NX x)
      ∧ map (permute p) names = names'
      ∧ equal NY (apply_renaming NY p (g (names, x))) (g (names', x))

With the quantifier, a new statement, proved for any equivariant `g`
(`fresh_choice`): the result with the made names bound is one
abstraction.

    И[n] names, И[n] names',
      equal_abstraction list_of_names NY
        (create names (g (names, x))) (create names' (g (names', x)))

### The answer

**It can be used, as it is in the papers.** `И a, P a` is defined (there
is a finite list of names off which `P` holds), Rocq accepts the letter
in a notation, and 50 statements about it are proved in three pairs of
files, with no axiom and no `Admitted`. Nothing that exists is changed.

**A result came with it.** N1 had left open the converse of "the
validator's comparison accepts alpha-equivalent terms". With the rules
that compare two binders at one fresh name it is proved
(`FlambdaCompareConverseSpec.v`): for terms whose code is closed and
whose binders repeat no name, the comparison accepts two terms exactly
when they are alpha-equivalent (`expr_eqb_iff_alpha_equivalent`). So
the comparison decides alpha-equivalence; and a `Let` is a name
abstraction in the sense of the papers: two `Let`s are alpha-equivalent
exactly when they have the same kind, the same defining expression and
`И z, (x z)·body ~ (x' z)·body'` (`alpha_let_iff`). The same is proved
of every other binder: the continuation of a `Let_cont`, the
parameters of its handler and the binders of code
(`FlambdaAlphaFreshSpec.v`), and the continuations of a recursive
`Let_cont` (`FlambdaAlphaGroupSpec.v`), which is also shown to be a
name abstraction of N1's interface, the one binder that was not: for
groups whose binders repeat no name, the abstractions are equal
exactly when the terms are alpha-equivalent.

**It makes some statements easier, and they are the ones about
equality, not the ones about rewrites.** The rule that comes out of the
survey:

- Use it where a statement says **two things are the same up to the
  choice of bound or fresh names**. There a proof shows the property
  for one fresh name and a user needs it for whichever name is at hand;
  the quantifier says both at once and the theorem that the two agree
  (`some_any`) does the work. Four places. The first is an
  equivalence with what stands, and so is the fourth for a `Let`; the
  second follows from what stands and the third is new. The table of
  section 4 says exactly what is proved of each.
  1. Equality of name abstractions: **equivalent** to what stands.
     N1's `equal_abstraction` is, for one bound name, exactly the
     definition of the papers: `[a]x = [b]y` if and only if
     `И c, (a c)·x = (b c)·y` (`equal_abstraction_fresh`). For a list
     of bound names that repeats none it is the same with as many
     fresh names (`equal_abstraction_names_fresh`). N1's
     `pattern_match_pair` is then the some/any theorem. Abstractions
     of one name with this equality obey every law of the interface
     (`fresh_abstraction_nominal`).
  2. Functions defined through `pattern_match`: the form with the
     quantifier **follows from** what stands, for one bound name
     (`concretion_well_defined`); it is not shown to give it back.
     The premise "no bound name is free in the result" is equivalent
     to the freshness condition for binders of the papers
     (`freshness_condition`).
  3. Functions that make fresh names (the join, inlining at fresh
     names): a **new** law, proved for any equivariant function
     (`fresh_choice`). No statement of the join's equivariance is in
     the tree yet for it to be compared with. For inlining it is
     proved of the terms (`FlambdaInlineFreshSpec.v`): a call refines
     its code inlined at fresh variables, with no premise about
     capture, and two choices of the variables give alpha-equivalent
     terms (section 4.6).
  4. The rules of alpha-equivalence at a binder, in the form in which
     two terms are compared: **rules that `alpha_equivalent` obeys**
     (`alpha_let_fresh`, and the same for a `Let_cont` and for
     parameters). They are introduction rules. Each is also read
     backwards, so it is an equivalence, on terms with closed code and
     distinct binders: for a `Let` (`alpha_let_iff`), for the
     continuation of a non-recursive `Let_cont` and the parameters of
     its handler, for the binders of code (`alpha_let_cont_iff`,
     `alpha_code_iff`), and for the continuations of a recursive
     `Let_cont` (`alpha_let_cont_recursive_iff`).
- Do **not** use it for **statements about a rewrite or an extracted
  function**. The six binder statements of `FlambdaNominalSpec.v`, the
  contract of the join, `fresh_name_fresh`, inlining as it is: each
  already is the reading "for every name outside a set" with the set
  written down, and for any permutation, not only a swap. The
  quantifier would hide the set, and whoever holds a particular name
  (a function calls `fresh_name` on the names to avoid and gets one
  name) needs the set to use the statement. The forms with the
  quantifier follow from the explicit ones in a few lines (three are
  proved); going back needs the support and gives a little less.
- It has nothing to say about the validator's comparison as stated
  (it pairs names and never makes one) or about T1's `rename_type`
  (types have no binder).

**Recommendation.** Adopt it as a derived layer, not as the primary
form: the explicit definitions and statements stay as they are and as
they are signed, and the three new pairs of files land as a leaf. For
new statements of the four kinds above, write the form with the
quantifier as the statement a reviewer reads and keep the explicit
form as the lemma that proves it.

**What each choice costs.**

- *The derived layer (recommended).* No statement changes text, no
  proof is replayed and nothing signed is reread; R1 reads three new
  Spec files, and two headers gain a sentence each.
- *The quantifier as the equality of name abstractions of one name
  (the bolder choice, and cheap).* The instance exists and obeys every
  law (`fresh_abstraction_names`, `fresh_abstraction_nominal`), so when
  the variable of a `Let` and the continuation of a `Let_cont` are made
  instances of the interface (N1's step 5, not yet done) they can take
  it as their equality, with the form by permutations as a lemma;
  nothing signed is reread, because nothing uses the generic equality
  for those binders yet. Binders of a list of names keep the form by
  permutations: with the quantifier their equality is right only for
  lists that repeat no name, which the type does not say.
- *The quantifier as the primary form everywhere.* Not possible for
  the generic interface (an abstract bindable has no fresh copy) nor
  for the statements about rewrites (section 4.3); for the rules of
  `alpha_equivalent` it would mean replaying every proof by induction
  on a derivation and R1 rereading `FlambdaAlphaSpec.v`, for no
  statement that is not already had as a lemma (section 5).

**What it is worth.** The model can now say, in the notation of the
papers and as a theorem about the same definitions that mirror the
compiler's `nominal/` directory, that its name abstractions are those
of nominal sets. That is the sentence in the comment of
`name_abstraction.mli` ("the equivalent of an atom abstraction
construction in nominal sets"), proved.

**Decided overnight** (for the human to confirm): the names
(`for_fresh`, `supports`, `propositions`, `concretion`); that lists of
bound names are treated when they repeat no name, which is row 5 of
well-formedness; that the explicit forms stay primary.

## 2. What is in the files

All in `middle_end/flambda2/rocq/`. Each Spec file says in its header
what to review it against.

| Files | Statements | What |
|-------|-----------:|------|
| `FlambdaFreshQuantifierSpec.v`, `Proofs` | 28 | The quantifier and its laws; `fresh_names` |
| `FlambdaFreshAbstractionSpec.v`, `Proofs` | 11 | Name abstractions, `pattern_match` and functions that make names, by the quantifier |
| `FlambdaFreshBindersSpec.v`, `Proofs` | 11 | The binders of the terms: opening at a fresh name, comparing two binders at one fresh name |
| `FlambdaCompareConverseSpec.v`, `Proofs` | 3 | The comparison accepts only alpha-equivalent terms; a `Let` as a name abstraction |
| `FlambdaAlphaFreshSpec.v`, `Proofs` | 6 | The other binders that are not recursive as name abstractions: alpha-equivalence at each is agreement of the scopes at fresh names |
| `FlambdaAlphaGroupSpec.v`, `Proofs` | 6 | The continuations of a recursive `Let_cont`: the same equivalence, and the group as a name abstraction of N1's interface, equal to another exactly when the terms are alpha-equivalent; lists of things that contain names |
| `FlambdaInlineFreshSpec.v`, `Proofs` | 7 | Inlining a call at fresh variables: the refinement with no premise about capture, and that the choice of the variables does not matter |

The first two mention no term of Flambda 2 and depend only on N1's
interface (`FlambdaNameAbstractionSpec.v`). (`fresh_names` and the
statement that its names are fresh moved from the Proofs file of the
first into its Spec file after it was merged, a function that makes
names having to be read; R1 approved it.) The other five depend on
the term-level files as they are after N1's step 3b and the
statements that follow it. All seven are on the integration branch
(the series that ends at 1160b780f0; the three statements that came
after its review, the two of inlining in a state and
`group_abstraction_iff`, at 909cda2dd4 and c88adfa3ba). They are
written for the terms as C2's epoch made them: a `Let` has the kind
of its variable, a handler and code their metadata, and the two sides
of a rule that compares two binders have the same kind or metadata,
as the comparison asks.

**The quantifier.** `for_fresh P` is
`∃ avoid, ∀ name, among name avoid = false -> P name`. Why this form:
it names no support; the list bounds the exceptions without being
exactly them, so nothing has to be decidable and no law needs the
excluded middle; it is a proposition, so nothing can compute a name
from it, which is right, since the extracted functions take the names
to avoid and call `fresh_name`. It is the cofinite quantification of
locally nameless developments with names in place of indices.

The laws, and which need a support (`supports N support P`: a
permutation that fixes the names of `support` keeps `P`):

| Law | Needs a support |
|-----|-----------------|
| Introduction; elimination (a witness outside any finite set); monotonicity | no |
| Conjunction; a proposition that does not mention the name | no |
| Disjunction, negation, `∀`, `∃`: one direction each | no |
| Two quantified names are different names | no |
| The three readings agree (`some_any`): all but finitely many; every name outside the support; some name outside the support | yes |
| Disjunction and negation, the other direction; implication | yes |
| Exchanging two quantified names (`for_fresh_swap`) | yes |

In the papers every predicate has a finite support. In Rocq a
predicate can look at the order of names, and then the laws that need
a support fail: `И a b, a < b` holds and `И b a, a < b` does not
(`for_fresh_swap_needs_support`). This is the same discipline as
"compare names by equality only".

With N1's interface: `Prop` is a type that contains no names, with
`<->` as its equality (`propositions`), so N1's `equivariant` and
`respects_equal` apply to a predicate as they stand; an equivariant
predicate is supported by the free names of its argument
(`equivariant_supports`), and the three readings agree with that
support (`some_any_nominal`).

**Several names.** `И[n] names, P names`: `P` holds of every list of
`n` different names outside a finite set (`for_fresh_names`). It
implies the quantifier taken `n` times, and is equivalent to it for a
predicate with a support; some/any holds for it.

## 3. The notation and the tools

- The letter is the Cyrillic capital I (U+0418). Rocq accepts it in a
  notation and prints it back in goals and in `Print`.
- For Rocq's lexer it is a letter, not a symbol. So the notation makes
  it a keyword, and a blank must follow it: `И a, P`. Rocq's own
  `Utf8_core` does the same for `λ`. Nothing in the tree used it as an
  identifier.
- It takes binders as `∀` does: `И a b, P`, `И (a : positive), P`.
- `make claims` and `make assumptions` are unaffected; the commit
  hooks accept it.
- The check of line lengths (`scripts/80ch.sh`) looks at OCaml files
  only and `make fmt` does not touch `.v` files. The 80 columns of
  `rocq/HACKING.md` are kept by counting characters; the letter is one
  character and two bytes.
- `rocq/review-pdf.pl` declares each Unicode character that the review
  document typesets; the integrator has added the line for this one.

## 4. The survey

"Equivalent" means proved in both directions. "Follows" means the form
with the quantifier is proved from the form that stands.

| Statement as it is | With the quantifier | Proved | Shorter or clearer? |
|--------------------|---------------------|--------|---------------------|
| N1 `equal_abstraction` (two opening permutations) | `И c, a @ c = a' @ c` for one name; `И[n] cs` for a list that repeats no name | equivalent (`equal_abstraction_fresh`, `equal_abstraction_names_fresh`) | Yes: it is the textbook definition. Stays a derived view: see 4.1 |
| N1 `pattern_match_pair_statement` | for one name it is the "any" reading of the line above | equivalent (`equal_abstraction_some_any`, `pattern_match_pair_fresh`) | Yes |
| N1 `pattern_match_well_defined_statement`: the premise that no bound name is free in the result | `И name, ∀ ab, name bound in ab -> name not free in f ab` | equivalent for an equivariant `f` (`freshness_condition`) | The same length; it is the form of the papers and asks less to check (one fresh name) |
| the same: the conclusion, for all opening permutations | `И c c', f (c, a @ c) = f (c', a' @ c')` for one name | follows (`concretion_well_defined`) | Yes: no permutation and no `opens` |
| N1 `fresh_name_fresh_statement` | none: see 4.2 | | No |
| `freshen_let_statement`; `rename_let_cont_statement` and `rename_handler_params_statement` at a swap | `И fresh, Let x kind d body ≡ Let fresh kind d ((x fresh)·body)`, and the like | follows (`freshen_let_fresh`, `freshen_let_cont_fresh`, `freshen_handler_params_fresh`) | Shorter by one premise. Less useful: see 4.3 |
| `rename_let_statement` and the five others, for any renaming | none: one name does not say a permutation | | No |
| `unused_let_statement` and the two after it | none: the premise is about the bound name of the term, not a fresh one | | No |
| `Alpha_let` and the other binder rules of `alpha_equivalent` (one binder renamed, with premises on the renaming) | two binders compared: `(И z, (x z)·body ~ (x' z)·body') -> Let x kind d body ~ Let x' kind d body'` | the rule is one that `alpha_equivalent` obeys (`alpha_let_fresh`, `alpha_let_cont_fresh`, `alpha_handler_fresh`), from the form with one fresh name (`alpha_let_at`, ...); it is an equivalence for every binder (`alpha_let_iff`, `alpha_let_cont_iff`, `alpha_code_iff`, `alpha_let_cont_recursive_iff`) | Yes for a reader; proofs use the form with one name: see 4.4 |
| the validator's comparison, `expr_eqb_sound_statement` | none in the statement; on names, pairing is exchanging for a fresh name (`names_match_fresh`) | on names only | No: see 4.5 |
| inlining, `inline_let_code_statement` with `inlinable` | a new statement, not a restatement: for fresh variables the call refines the code opened at them, inlined (see 4.6) | proved (`inline_at`, `inline_fresh`, `inline_at_fresh`; `inline_at_choice`, `inline_fresh_choice`) | It removes the two premises about capture |
| the join's contract (T5), with the names to avoid | no gain for the contract; a gain for "the choice does not matter" (`fresh_choice`) | the generic statement is proved; the join's is T5's | See 4.7 |
| T1 `rename_type` and its laws | none: types have no binder and no statement has a freshness premise | | No. Types become an instance to which `some_any_nominal` applies |

### 4.1 Abstractions: why the form with permutations stays the definition

For one bound name the two definitions are the same relation, and the
proof is short in both directions: forwards by `pattern_match_pair` at
the two swaps, backwards the two swaps are the permutations asked for.
The support is the free names of the abstractions, not of the scopes,
so the bound name itself is allowed, as in the papers.

For a list of names two limits appear, and they decide the matter.

- The permutation that sends the bound names `bs` to fresh names `cs`
  is the swaps `(b1 c1) ... (bn cn)`. It does that only if `bs`
  repeats no name and `cs` has no name of `bs`. So the statement asks
  that the bound names be distinct (row 5 of well-formedness,
  `FlambdaBindersSpec.binders_distinct`, which every well-formed term
  meets; N1's interface itself allows a repeated name), and the set
  that the quantifier hides contains the bound names, which it does
  not for one name.
- For a bindable in general there is no such statement. N1's
  `bindable` has no way to make, from a bindable and fresh names, the
  permutation that sends the one to the others. The compiler's
  `Bindable.S` has `renaming` for that; adding it to the interface is
  possible and is not proposed here.

So `equal_abstraction` by permutations is the definition for every
bindable, and the quantifier is a second reading for the two bindables
that the terms have. The literature on binders of several names
(Urban and Kaliszyk, Nominal Isabelle) also defines the equality with
a permutation. N1 agrees.

### 4.2 `fresh_name` and what the quantifier cannot say

`fresh_name_fresh` says that the name the function returns is outside
the list it was given. A statement with the quantifier is about all
but finitely many names and has no place for a function: from
`И a, P a` nothing follows about `fresh_name names` for a given
`names`, because the exceptions are hidden. The link is one lemma each
way: elimination of the quantifier is proved with `fresh_name`
(`for_fresh_elim`), and for a predicate with a support the name that
`fresh_name` returns satisfies it as soon as the list given contains
the support (`some_any`). A specification of an extracted function
stays in terms of the names to avoid.

### 4.3 The binder statements: the explicit form says more

Each of the six statements is: for every renaming that fixes the free
names of the scope other than the bound ones, the binder may be
renamed. Against the form with the quantifier:

- It is for any permutation. The quantifier speaks of one name (or
  `n`), that is, of a swap.
- It names the set. A rewrite that has a name in hand, and every
  extracted function has, must know that its name will do; with the
  quantifier it would need the "any" reading, that is, the support,
  which is the premise it started from.
- The set it names is tight. `freshen_let` allows a new name that
  occurs in the defining expression, since that is outside the scope.
  The general argument from the quantifier (a predicate is supported
  by the free names of everything it mentions) gives the statement
  back only for names outside the defining expression too.

From the explicit form to the quantifier is two lines once the free
names are a list (`fresh_not_free`). So: the explicit statements stay;
the three forms with the quantifier are there for a reader, and for a
proof that needs "for some fresh name" as a hypothesis.

### 4.4 Alpha-equivalence at a binder

`alpha_equivalent` has one rule for each binder that renames it on one
side. To compare two terms one wants the rule with two sides. It is
proved in two forms. With one name:

    code_closed body = true -> code_closed body' = true ->
    among z (free_variables_of_expr body) = false ->
    among z (free_variables_of_expr body') = false ->
    alpha_equivalent ((x z)·body) ((x' z)·body') ->
    alpha_equivalent (Let x kind d body) (Let x' kind d body')

and with the quantifier, the same without the two lines on `z`. The
second is the first with its side conditions hidden. For the converse
of the comparison (section 6) the first is the one to use: it asks for
one name, which `fresh_name` gives, and one use of the induction
hypothesis. The quantifier would be the right premise if the rule were
a constructor of an inductive definition, where the induction
hypothesis must be had for every fresh name; that is the usual reason
for cofinite quantification, and it does not arise here because
alpha-equivalence is generated by its one-sided rules.

The rule can be read backwards for a `Let`: if two `Let`s are
alpha-equivalent then they have the same kind and the same defining
expression and their bodies are alpha-equivalent at a fresh name
(`alpha_let_iff`, for closed code and distinct binders). The proof
goes through the comparison and its converse (section 6).

The same holds of the other binders that are not recursive
(`FlambdaAlphaFreshSpec.v`), with the same proof. `h` and `h'` being
handlers, `alpha_handlers h h'` says that they have as many
parameters, the same metadata (the kinds of the parameters) and
`И[n] zs, (params zs)·handler ~ (params' zs)·handler'`; and
`alpha_code c c'` says the same of two pieces of code, with fresh
variables for `my_closure` and the parameters and two fresh
continuations for the return and exception continuations.

    Let_cont k h body ~ Let_cont k' h' body'
    <-> alpha_handlers h h' ∧ И z, (k z)·body ~ (k' z)·body'

    Let_static (before ++ Bind_code id c :: after) body
    ~ Let_static (before ++ Bind_code id c' :: after) body
    <-> alpha_code c c'

    Let_static bindings body ~ Let_static bindings' body'
    <-> Forall2 alpha_binding bindings bindings' ∧ body ~ body'

(`alpha_let_cont_iff`, with `alpha_let_cont_body_iff` and
`alpha_handler_iff` for each binder alone; `alpha_code_iff`;
`alpha_let_static_iff`, where `alpha_binding` asks the same code id
and `alpha_code`, or the same symbol and constant.) So at every binder
that is not recursive alpha-equivalence is the equality of name
abstractions of the papers.

What each direction takes. From right to left (the rule): closed code,
and that the lists of bound names compared repeat no name; nothing of
the binders within the scopes. From left to right: both conditions on
both terms, because the proof goes through the comparison. The premise
on the lists cannot be left out: `alpha_handlers` holds of the handler
`(x, x) -> jump x` against `(y, y') -> jump y'`, because the swaps of
a list that repeats a name send it to the last of its fresh names, and
the two `Let_cont`s that have them are not alpha-equivalent, by N1's
statement that alpha-equivalent terms have their binders distinct
together (`alpha_handlers_repeated_parameter`).

The continuations of a recursive `Let_cont` are bound in every handler
and in the body (`FlambdaAlphaGroupSpec.v`). `ks` being the
continuations of the first group and `ks'` those of the second:

    Let_cont_recursive handlers body ~ Let_cont_recursive handlers' body'
    <-> length handlers = length handlers'
        ∧ И[n] zs,
            Forall2 alpha_handlers ((ks zs)·handlers) ((ks' zs)·handlers')
            ∧ (ks zs)·body ~ (ks' zs)·body'

(`alpha_let_cont_recursive_iff`; the handlers are compared in order.)
The proof exchanges the continuations of each group for the fresh ones
by a renaming of the whole term, which fixes its free names, and then
compares two groups that bind the same continuations.

The group is also a name abstraction of N1's interface
(`group_abstraction`): the bound names are the list of its
continuations, the scope is the list of its handlers and its body, and
two abstractions that are equal in N1's sense give alpha-equivalent
terms. A handler in the scope is an abstraction of its parameters
(N1's `handler_abstraction_statement`) with its metadata, equal to
another when the metadata is the same and the abstractions are equal,
so no premise of distinct names is needed. The scope is a thing
that contains names with all the laws
(`group_continuations_nominal`); for that the interface needed lists,
which are given for any things that contain names (`list_names`,
`list_nominal`). With this every binder of the table of `NAMES.md`
section 3 is a name abstraction of the interface.

For groups whose binders repeat no name the converse holds, so the
two accounts are one relation (`group_abstraction_iff`): the
abstractions are equal in N1's sense exactly when the terms are
alpha-equivalent, that is, by `alpha_let_cont_recursive_iff`, exactly
when the groups agree at fresh continuations. The proof takes the
fresh continuations and the fresh parameters that the agreement
gives and uses them as the permutations that open the abstractions;
it needs the parameters of each handler distinct, which is why the
premise is there in this direction and not in the other.

### 4.5 The validator's comparison

`expr_eqb` keeps pairs of bound names and makes no fresh name; neither
its definition nor `expr_eqb_sound_statement` has a freshness premise
or an avoidance list. The compiler's `Compare` does it the other way:
it opens both binders at one fresh name (`pattern_match_pair`). That
the two ways agree is a statement with the quantifier:

    expr_eqb ((x, x') :: vm) km body body'
    = expr_eqb vm km ((x z)·body) ((x' z)·body')    for a fresh z

On names it is proved (`names_match_fresh`: to pair two names is to
exchange each for one fresh name). On expressions the direction that
the converse needs is proved with it (`opened_eqb` in
`FlambdaCompareConverseProofs.v`), from N1's lemmas rather than by a
new recursion: what the comparison accepts under the pairs of the
bound names it accepts with no names paired, once the bound names of
both sides are exchanged for the same fresh names.

### 4.6 Inlining

`inline_statement` and `inline_let_code_statement` take
`inlinable ap c r`, of which two conjuncts say that binding the
parameters and `my_closure` captures nothing in the arguments.
Simplify has no such premise because it opens the code at fresh names
(`Function_params_and_body.pattern_match` in
`Inlining_transforms.inline`). `FlambdaInlineFreshSpec.v` says that,
for a call with the binding of its code in sight:

    inlinable_at_fresh ap c r ->
    length fresh = length (code_variables c) ->
    distinct_outside
      (code_variables c ++ free_variables_of_simples (ap_args ap)) fresh ->
    expr_refines (Let_static [Bind_code called c] (Apply ap))
      (Let_static [Bind_code called c] (inlined_at fresh c r ap))

`inlined_at fresh c r ap` is `inlined_body` of the code with
`my_closure` and the parameters exchanged for `fresh`
(`open_code fresh c`), and `inlinable_at_fresh` is `inlinable` without
the two conjuncts about capture, with closed code said by
`code_is_closed` and the variables of the code distinct. This is the
explicit form (`inline_at`). Then:

- the function, which takes the names to avoid and makes the variables
  by `fresh_names`: `inlined_fresh avoid c r ap`, which the call
  refines when `avoid` has the free variables of the arguments
  (`inline_fresh`);
- with the quantifier: `И[n] fresh, expr_refines ... (inlined_at fresh
  c r ap)` (`inline_at_fresh`), which follows and says less;
- the choice does not matter: two lists of fresh variables, or two
  lists of names to avoid, give alpha-equivalent terms
  (`inline_at_choice`, `inline_fresh_choice`).

The last is the fourth form of `NAMES.md`, section 7 ("its statement
relates two choices by the permutation that swaps them"), as it comes
out when the names made are bound in the result: the swap of the two
lists is a renaming that fixes the free variables of the first result,
so the two results are alpha-equivalent (`Alpha_rename`). They are not
the second equal to the first renamed, because a fresh variable is
outside the free variables of the body only and may be one that the
body binds.

The proof of the refinement is three steps, each a statement that
stands: the binders of closed code are renamed where the code is
bound (N1's `rename_code_binders`); the opened code meets `inlinable`;
and the code is renamed back. So nothing of the machine is used.

The same is given of a state, as `inline_statement` is, for a pass
that inlines the calls of the code it has seen bound
(`inline_at_state`, `inline_fresh_state`):

    ap_call_kind ap = Direct called ->
    lookup called (static_code statics) = Some c ->
    inlinable_at_fresh ap c r ->
    length fresh = length (code_variables c) ->
    distinct_outside
      (code_variables c ++ free_variables_of_simples (ap_args ap)) fresh ->
    refines (State (Apply ap) vars conts statics)
      (State (inlined_at fresh c r ap) vars conts statics)

The proof is the same three steps with the code replaced by the
opened code in the static environment: two static environments that
have, at each code id, code that the comparison accepts give
equivalent states (the bisimulation of `FlambdaCompareProofs.v`).

Not done: an `inline_calls` that freshens, which would take the names
to avoid and whose statement would be the "any" reading. It is a pass
of the validator, and its owner (V2) does not want one now: no call
of the validator's examples is refused because of capture (V2
counted, over 462 units, before Simplify and after each round of the
validator's normalisation: the only calls with an argument that
mentions `my_closure` or a parameter of the code called are recursive
calls in the body of the code itself, which are not inlined). If a
case appears, V2 changes the function that inlines one call and needs
from here only that its test gives `inlinable_at_fresh`.

### 4.7 The join

T5's contract (`flambda2-rocq/T5-join`, `FlambdaJoinSpec.v`) is about
a function `join avoid inputs`. `avoids_known` asks that `avoid`
contain every variable that the source or a use knows, and
`join_introduces` promises that a variable of the target that the
source does not know is imported from a use or is outside `avoid`. T5
and N1 agreed that its equivariance be stated "up to an explicit
permutation of the names the join makes". Tested as N1 asked:

- **The contract.** With the quantifier it would be about a variant
  `join_at names inputs` that is given its names: for all but finitely
  many lists of names, the guarantees hold. Three things are against
  it. The hidden set is `avoid`, so it is the same sentence with the
  set not shown. The number of names the join makes is not known
  before it runs, so `И[n]` has no `n`, and a supply would come back.
  And the function that is extracted and compared with the compiler's
  computes one result. So: no gain, as N1 expected.
- **From all fresh names to the names chosen.** If a contract is
  proved for every list of different names outside the free names of
  the inputs, it holds for the names that `fresh_name` gives when the
  names to avoid include those free names. That is
  `some_any_names_nominal`, and it asks that the guarantee be an
  equivariant predicate, which is T1's and T2's equivariance of the
  meaning of types and environments.
- **The choice does not matter.** This is where the quantifier is
  better. `fresh_choice`: for an equivariant `g`,

      И[n] names, И[n] names',
        equal_abstraction list_of_names NY
          (create names (g (names, x))) (create names' (g (names', x)))

  The result with the made names bound is one abstraction. No
  permutation is in the statement; the proof builds it (the swaps of
  the first names with the second, which fix the free names of the
  inputs because an equivariant function invents no name). For the
  join as extracted the same is said of two lists of names to avoid.
  It costs the extraction nothing: `g` is a way to state, not a change
  of the function.

## 5. What it would cost to make it the primary form

Not recommended; for the record.

- `equal_abstraction` cannot be replaced in N1's interface: it is
  defined for any bindable (section 4.1). For one bound name the
  equality with the quantifier is there as an instance of the interface
  with its laws (`fresh_abstraction_names`), to be chosen or not where
  such a binder is made an instance; that is the cheap part.
- `pattern_match_pair_statement` and
  `pattern_match_well_defined_statement` would keep their text (they
  are about any bindable and any opening permutation) and gain the
  corollaries that exist now.
- In `FlambdaNominalSpec.v` nothing can be replaced (section 4.3).
- In `FlambdaAlphaSpec.v` the rules of `alpha_equivalent` could be
  replaced by two-sided rules with the quantifier. Every proof by
  induction on a derivation would be replayed (equivariance, the free
  names, soundness, in `FlambdaAlphaProofs.v`, and the containment in
  the comparison, in `FlambdaCompareAlphaProofs.v`), the
  induction principle would have to be written by hand (the
  quantifier is an existential under which the relation occurs), and
  R1 would reread the file. What stands is equivalent for the purpose
  (section 4.4).
- T1 and T3 are writing instances of N1's interface tonight; a change
  of its fields would stop them.

## 6. What it gives the proofs still to come

- **Step 3b, the renaming enters code.** Nothing directly. These files
  sit on it and needed nothing but the premise that code is closed,
  which the statements they restate have.
- **The converse of the comparison**: proved
  (`FlambdaCompareConverseSpec.v`). For closed code and distinct
  binders, `expr_eqb [] [] e e' = true` gives `alpha_equivalent e e'`.
  The proof is the compiler's `pattern_match_pair` as an argument: by
  recursion on the first term, at each binder the bound names of both
  sides are exchanged for the same fresh names, the scopes are then
  accepted with no names paired, the recursion gives that they are
  alpha-equivalent, and the rule that compares two binders at those
  names concludes. What the quantifier gave it is that shape and the
  two-sided rules. The proof itself uses the forms with one fresh name
  and takes its names from `fresh_name`; the letter does not occur in
  it, which is what section 4.4 expected.
- **The join.** `fresh_choice` and `some_any_names_nominal` are stated
  for any equivariant function of names and an argument, so T5 can use
  them when the join's equivariance is proved: the statement that the
  join does not depend on the names it makes needs no permutation in
  it, and a contract proved for all fresh names gives the contract for
  the names chosen.
- **Types and environments** (T1, T2). Once types are an instance of
  the interface (T1 has the laws, with `=` as the equality),
  `some_any_nominal` applies to every equivariant judgement about
  them, `type_satisfied` for one. Two things there are binders
  (N1-6): the extra variables of an extension that declares variables,
  and the variables that a level defines. (The names that an ordinary
  environment extension has equations for are not: nothing declares
  them, and a renaming renames them like any free name.) If T2 makes
  those two name abstractions over a list of distinct variables,
  `equal_abstraction_names_fresh` is their equality.
- **Inlining that freshens** (with S4): section 4.6.

## 7. Before and after, more

Section 1 has three. The first again in full, and two for the terms.

**Equality of abstractions.** N1, as it stands and stays:

    Definition equal_abstraction (a a' : name_abstraction B T) : Prop :=
      ∃ p p' : permutation,
        opens p a
        ∧ opens p' a'
        ∧ fst (pattern_match p a) = fst (pattern_match p' a')
        ∧ equal NT (snd (pattern_match p a)) (snd (pattern_match p' a')).

With the quantifier, proved equivalent for one bound name:

    equal_abstraction single_name NT a a'
    <-> И fresh, equal NT (concretion NT a fresh) (concretion NT a' fresh)

**A function of an opened abstraction.** N1's conclusion:

    equal_abstraction NB NT a a' ->
    opens NB NT p a ->
    opens NB NT p' a' ->
    equal NX (f (pattern_match NB NT p a)) (f (pattern_match NB NT p' a'))

With the quantifier, for one bound name:

    equal_abstraction single_name NT a a' ->
    И fresh fresh',
      equal NX (f (fresh, concretion NT a fresh))
        (f (fresh', concretion NT a' fresh'))

**Opening a `Let`.** `FlambdaNominalSpec.v`, as it stands and stays:

    ∀ (x fresh : variable) (kind : flambda_kind) (defining_expr : named)
      (body : expr),
      code_closed body = true ->
      ~ var_free_in_expr fresh body ->
      expr_equivalent (Let x kind defining_expr body)
        (Let fresh kind defining_expr
           (rename_expr (Renaming [(x, fresh)] []) body))

With the quantifier:

    ∀ (x : variable) (kind : flambda_kind) (defining_expr : named)
      (body : expr),
      code_closed body = true ->
      И fresh,
        expr_equivalent (Let x kind defining_expr body)
          (Let fresh kind defining_expr
             (rename_expr (swap_variable x fresh) body))

**Two `Let`s compared.** New, in both forms (section 4.4).

## 8. What is not done

- An `inline_calls` that freshens (section 4.6): its owner does not
  want one now. The refinement itself is done in both forms, with the
  binding of the code in sight and with the code in the static
  environment of a state.
- The form with the quantifier for a list of bound names that repeats
  a name ("the two lists repeat alike"). N1 does not want it:
  well-formedness excludes such lists.

## 9. The statements written with the older accounts of free names

`NAMES.md`, section 9: the relations `var_free_in_expr` and
`cont_free_in_expr`, `FlambdaWellFormedSpec.free_continuations` and
`FlambdaNormaliseSpec.expr_in_scope` do not look into code, and the
functions of `FlambdaBindersSpec.v` do; they agree where code is
closed (`FlambdaFreeNamesSpec.v`). This is the list of what is written
with the older accounts, for the change in which they are deleted. No
statement is duplicated here. In the forms below `fv` and `fc` are
`free_variables_of_expr` and `free_continuations_of_expr`.

| File (owner) | Statement or definition | Written with | The form it would take |
|--------------|-------------------------|--------------|------------------------|
| `FlambdaNominalSpec.v` (N1) | `rename_let_statement` | "`y <> x`, `var_free_in_expr y body`" and "`cont_free_in_expr k body`", each implying that `r` fixes the name | `r` fixes every name among `without [x] (fv body)` and among `fc body` |
| | `freshen_let_statement` | `~ var_free_in_expr fresh body` | `among fresh (fv body) = false` |
| | `rename_let_cont_statement` | as `rename_let_statement`, for `k` | `r` fixes `fv body` and `without [k] (fc body)` |
| | `rename_handler_params_statement`, `rename_recursive_handler_params_statement` | "`y ∉ params`, `var_free_in_expr y handler`" | `r` fixes `free_variables_of_handler (Handler params handler)` and `fc handler` |
| | `rename_let_cont_recursive_statement` | the two relations at the whole term | `r` fixes `fv` and `fc` of the whole term |
| | `unused_let_statement`, `unused_let_cont_statement` | `~ var_free_in_expr x body`, `~ cont_free_in_expr k body`; no premise on code | `among x (fv body) = false`, `among k (fc body) = false`. The new premise asks more where code is not closed, so the statements stay true with no premise on code; the proof needs "free by the relation implies among the list" without closed code, which is not stated today |
| | `unused_let_cont_recursive_statement` | `cont_free_in_expr k body -> lookup k handlers = None` | `among k (fc body) = true -> lookup k handlers = None` |
| | the relations themselves, and `var_free_in_named`, `var_free_in_simples` and the like | | deleted |
| `FlambdaAlphaSpec.v` (N1) | the rules `Alpha_rename`, `Alpha_let`, `Alpha_let_cont`, `Alpha_handler`, `Alpha_recursive_handler` | as the statements of `FlambdaNominalSpec.v` | as those. Every proof by induction on a derivation is replayed (`FlambdaAlphaProofs.v`, `FlambdaCompareAlphaProofs.v`); the proofs that only use the rules need the new form of the premises (N1's instances; of N2's, `FlambdaFreshBindersProofs.v`, `FlambdaCompareConverseProofs.v`, `FlambdaAlphaGroupProofs.v`, `FlambdaInlineFreshProofs.v`) |
| | `alpha_let_cont_recursive_statement` | the two relations at the whole term | as `rename_let_cont_recursive_statement` |
| | `var_free_equivariant_statement`, `cont_free_equivariant_statement` | the relations | deleted: `free_variables_equivariant_statement` and `free_continuations_equivariant_statement` are the same of the functions |
| | `alpha_equivalent_free_names_statement` | the relations | `alpha_equivalent_free_variables_statement` and `alpha_equivalent_free_continuations_statement` are the same of the functions, with `same_names`; this one is deleted |
| | `rename_variables_equivalent_statement` | `cont_free_in_expr k e` | `r` fixes `fc e` |
| `FlambdaApplySpec.v` (the integrator, for S4) | `inlinable`, and with it `inline_statement` and `inline_let_code_statement` | closed code by the two relations; no capture by `var_free_in_simples` | `names_among (code_my_closure c :: code_params c) [ret; exn] (code_body c) = true` for the first two conjuncts; `among _ (free_variables_of_simples (ap_args ap)) = false` for the two about capture. `FlambdaInlineFreshSpec.inlinable_at_fresh` is written so |
| `FlambdaNormaliseSpec.v` (the integrator, for V1) | `expr_in_scope`, used by `inlinable_b` | a check of scope of its own | `names_among` (`expr_in_scope_agrees_statement`); `expr_in_scope` and its companions deleted |
| `FlambdaWellFormedSpec.v` (the integrator) | `free_continuations`, used by `handler_at_toplevel` | a function of its own | `free_continuations_of_expr` (`free_continuations_agree_statement`); the older function deleted |
| `FlambdaFreshBindersSpec.v` (N2) | `fresh_not_free_statement` | the two relations, under `И` | deleted: of the lists it is `for_fresh_avoids`, with no premise on code |
| `FlambdaFreeNamesSpec.v` (N1) | the four statements that the accounts agree | | deleted with the file, last |

Proofs that mention the relations, by file, for the size of the
change: `FlambdaAlphaProofs.v` and `FlambdaFreeNamesProofs.v` most;
then `FlambdaNominalProofs.v`, `FlambdaNormaliseProofs.v`; a few lines
each in `FlambdaApplyProofs.v`, `FlambdaCompareProofs.v`,
`FlambdaEquivarianceProofs.v`, `FlambdaNominalInstancesProofs.v`,
`FlambdaUnusedContsProofs.v`, the Proofs files of N2 named above, and
`FlambdaTypesProofs.v` of the types library.

The order that keeps every commit building: the statements of
`FlambdaNominalSpec.v` first, each proved from the one it replaces by
the agreement; then the rules of `alpha_equivalent`, with the proofs by
induction; then the three definitions of the other files; then the
relations and `FlambdaFreeNamesSpec.v`. N1 has said that it is to be
done when the older relations can be deleted in the same change, and
not while the term forms are changing.
