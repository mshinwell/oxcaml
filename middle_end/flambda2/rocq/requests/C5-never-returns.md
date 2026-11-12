# C5: calls that never return. A core change request

From C5, for C0 (who decides between the two forms of section 3, and
has the question of section 5), C3 (whose calls these are), V2 (the
test tool and the validator), R1 (the trust ledger) and P1 (who found
it, on units made from OCaml sources that are not in this tree).

It is a request and nothing else: no file of the model or of the tool
is changed with it. Section 6 says what was tried, with the tool
changed and not committed.

## Why

`let fail s = raise (Failure s)` is how most programs raise. When
Simplify does not inline such a function it marks each call of it as
one that never returns, and the call then has no return continuation.
The model has no such call, and the test tool refuses the whole unit
after Simplify ("not checked: the model has not got a call that never
returns"): the two runs are not compared and nothing is validated. A
function that always raises needs only to be called twice and be too
large to inline, or to be marked `[@inline never]`, for that.

## 1. What the compiler does

- **The term** (`terms/apply_expr.mli`). The result continuation of a
  call is `Return of Continuation.t | Never_returns`. `Never_returns`
  has no free name.
- **The front end** makes `Return` only
  (`from_lambda/closure_conversion.ml`).
- **Simplify** introduces it in one place
  (`simplify/simplify_apply_expr.ml`,
  `simplify_direct_full_application`, where the call is neither
  inlined nor made a jump to the head of its own loop): a direct full
  call gets `Never_returns` if it had it, or if the result types of
  the code called are `Bottom`. They are `Bottom` exactly when
  Simplify, traversing the body of that code, recorded no use of its
  return continuation, unless the code is opaque
  (`simplify/simplify_set_of_closures.ml`, `compute_result_types`:
  `| false, _, None -> Bottom`). So it is what is left of the body
  after Simplify that counts: a use in a branch that Simplify removed
  does not, nor does a tail call that itself never returns.
- Elsewhere Simplify only carries it. An over-application is split
  into a full call, which returns to a new continuation, and a second
  application, of the result to the arguments that remain, which is
  an indirect call (`simplify/simplify_common.ml`,
  `split_direct_over_application`). If the over-application never
  returns, the second application carries `Never_returns` where no
  region is needed around the two; where one is, it returns to a
  continuation whose handler ends the region and then is `Invalid`
  (`Over_application_never_returns`). So in a term after Simplify
  `Never_returns` can be on an indirect call (C3's correction).
  A partial application that never returns is a fatal error
  (`simplify_direct_partial_application`), and so is a method call.
  Inlining leaves the return continuation of the inlined body as it
  is, a name bound nowhere (`simplify_shared/inlining_helpers.ml`,
  `make_inlined_body`). A call of a function to itself that never
  returns counts as a tail call, for the making of loops.
- **The backend** (`to_cmm/to_cmm_expr.ml`, `apply_expr`, case 1)
  emits the call with nothing after it, as it does a call whose
  return continuation is that of the function it is in. Were the
  callee to return, its result would be taken for the result of the
  enclosing function.

So the compiler means: the callee does not return, and if it did the
program would have no meaning.

## 2. What the model must say

A call that never returns runs as any call does, and a return from it
is undefined. Nothing else changes: its exception continuation, its
arguments and the test of its arity against the code are those of a
call that returns.

This makes Simplify's claim something that a run and the validator
check. If the callee returns in the run before, the run after is
undefined where the run before is not, and the tool reports the
difference.

## 3. Two forms

**A. In the syntax.** `ap_continuation` gets the compiler's type
(`Return k | Never_returns`), and the machine gives a call that never
returns a continuation value that is undefined when applied. It is the
compiler's term, constructor for constructor. It is an epoch:
`ap_continuation` is read in 72 files of the model (free names,
renamings, the comparison up to names, every pass, the models of
Simplify), and the validator's inlining needs a case, since there is
then nothing to put for the return continuation of the inlined body.
C3's proposal for the machine: no new form of continuation value;
`step` gives `call_function`, for `Never_returns`, the closure of a
handler with no parameter, no kind and the body `Invalid`, under
empty environments. Applied to any values it is undefined, every
invariant on continuation values holds of it, and no proof by cases
on them gets a case.

**B. In the conversion only.** The test tool converts

    apply f (x) -> never * k_exn

to a call that returns to a continuation bound around it and nowhere
else, whose handler is `Invalid` and whose parameters are of the kinds
of the return arity of the call, which the call keeps; whatever the
kind of the call:

    Let_cont_non_recursive k (Handler params metadata Invalid)
      (Apply { ...; ap_continuation := k })

The model is not changed. A return applies the handler and is
undefined, which is section 2 exactly; a return of values of other
kinds is undefined as well. The cost is that the term of the model is
not the compiler's: nothing can be stated of the shape "this call has
no return continuation", the conversion back to the compiler's syntax
prints the continuation, and the trust ledger has a sentence more
(the conversion reads `Never_returns` as "a return is undefined").
One limit: Simplify counts a call of a function to itself that never
returns as a tail call; under B it returns to B's continuation and is
not one for `FlambdaLoopifySpec.loopify_unit`. It cannot arise in a
term before, where the front end makes `Return` only.

**Asked for: B now, A when `apply_expr` is next changed for another
reason.** B costs the model nothing. A is the right form in the end,
and is cheapest inside an epoch that already goes through every use
of a call; under A the validator's inlining would make B's handler
anyway. Going from B to A later changes the conversion and no
statement.

## 4. Who does what

- **C0**: the choice, and section 5. Under B nothing more.
- **C3** has confirmed: (1) a full call under B means what section 2
  says, for a direct call and an indirect one, provided that the
  converted call keeps the compiler's return arity and the handler
  has that arity, unarized, as its kinds (`call_code` compares the
  return arity of the call with the result arity of the code);
  (2) nothing is needed for partial applications (the compiler has
  none that never returns; in the model a call that is partial when
  it runs gives its partial application to the handler at once, and
  is undefined) nor for over-applications (in the model the full call
  inside one returns to what is left of the application, and only the
  last return reaches the handler); (3) for A, the form of section 3.
- **V2**: the conversion (B: the case `Never_returns` of
  `convert_apply`, a fresh continuation and fresh parameters; the
  sentence of the trust ledger, for R1), the round trip of the
  conversion, and the expected files.
- **The validator.** With the conversion alone the units are run and
  compared, and none is validated (section 6). It asks twice.
  - *Leaving the calls that the term after still has* (the first
    asking). The term before has a return continuation where the term
    after has B's handler; in one of the two units tried that is the
    only difference. The validator needs a rewrite of the term
    before: a direct full call of code whose body does not mention
    its return continuation is given B's handler. The lemma it rests
    on is that such code never applies its return continuation, so
    two calls that differ only in where they return to run alike. In
    the other unit the continuation that the call returned to then
    has a use fewer, and Simplify has made a constant of its
    parameter: whether the passes there are do the same after the
    rewrite is to be seen. The test is on the body as it is when the
    rewrite runs: code that Simplify finds never to return only after
    removing a branch, or because of a call in it that never returns
    (`let fail2 () = fail ()`), is reached in a later round, once the
    body has been normalised; where it is not reached the unit is not
    validated, which is safe. C5 can write this pass once the
    conversion is in.
  - *Inlining them on both sides* (the second asking). B's handler
    goes, as unused, and the term after is then less normalised than
    the term before: a continuation that only raises stays where the
    term before raises in place, and under a `try` the handlers of
    the term before are demoted and those of the term after are not.
    Whether the term after is to be normalised further after an
    inlining is V2's to say; with the rewrite these units do not
    need it.
- **N1**: the rewrite binds a continuation; it will be stated to
  commute with renaming, as the others are.
- **R1**: the sentence of the trust ledger; the Spec statement of the
  rewrite when it exists.

## 5. A static binding in an exception handler

A `try` at the toplevel of a unit whose body ends with such a call
never returns normally. Simplify then puts the rest of the unit, with
the binding of its module block, inside the exception handler: the
continuation after the `try` is applied once, by the handler, and
Simplify inlines it there. That term is not well-formed for the model
(`FlambdaWellFormedSpec.statics_at_toplevel`: a handler that is an
exception handler is not at toplevel), so the tool says "the term
after Simplify is NOT WELL-FORMED" and fails.

It is not B's doing, and needs no call that never returns: the tool
of the integration branch says the same today of

    let[@inline never] f x = if x then raise Not_found else 1
    let result =
      try
        let _ = f (opaque true) in
        let _ = f (opaque false) in
        raise Not_found
      with _ -> 2

The model's rule is Simplify's own on the way down
(`simplify/simplify_let_cont_expr.ml`, `at_unit_toplevel`; a `Let`
that binds a symbol elsewhere is a fatal error,
`simplify/simplify_named.ml`). Simplify does not keep it on the way
up: given its own output for that source, with the compiler's tool
that runs Simplify on a `.fl` file, it stops with that fatal error.
The compiler runs Simplify once, so nothing stops today. Discrepancy
C5-11; demonstrated with an unmodified compiler, not in this tree.

For C0, with the human: (a) keep the rule, and such a unit is reported
under that label and not checked further; or (b) let an exception
handler be at toplevel where its body can only leave through it or to
the exception continuation of the unit. The machine runs these terms,
and their two runs agree (section 6). (b) is a change to
`statics_at_toplevel` and to what is proved from it.

## 6. What was tried

With the tool of the integration branch, on sources written for this
(each function is called twice, or the front end inlines it):

| Source | Today |
|--------|-------|
| `let[@inline never] fail () = raise Not_found`, called twice at toplevel, each call under a handler that catches everything | not checked |
| the same without the attribute | validated: Simplify inlines it |
| the first, with `raise (Failure s)` of a parameter | not checked |
| the first, each call in an arm of a test and under no handler | not checked |
| the first, called from a second function that is not inlined | not checked |

With B's conversion in the tool (not committed):

- The fourth and the fifth are run before and after, the runs are the
  same, and they are not validated; section 4 says by what the two
  terms differ at each asking.
- The first and the third stop at section 5. With that check of the
  tool lifted as well, the first is run before and after and the runs
  are the same; the third is undefined before and after, as it makes a
  block with a symbol of another unit in it, which is bound to
  nothing (the cause of discrepancy V2-4).

So B alone turns "not checked" into two runs that are compared, for
every unit that section 5 does not stop; validation needs the rewrite
of section 4, and a `try` at toplevel around the call needs the answer
to section 5. The third needs the symbols of other units to be bound
besides.
