# The port of Simplify to Rocq: the guide for a porter

`simplify/DIR/foo.ml` of the compiler becomes `simplify_port/DIR/Foo.v`. Rocq
compiles it twice, against two files `Port_monad.v` with the same names:
`monad/real` (what the port MEANS: a monad of the world, fatal errors,
exceptions and fuel) and `monad/id` (`M A` is `A`). From the second build
Rocq extracts OCaml in direct style, by its extraction and directives alone;
no tool changes Rocq's text. ocamlformat formats it and OCaml checks its types
against the compiler's interfaces: `extracted/DIR/foo.ml`, which is committed
and should read like the compiler's file. `Simplify_expr.v` and
`Simplify_apply_cont_expr.v` are the models: read them and their extracted
files beside the donors first. Points marked HUMAN are the human's to judge.

## 1. The file

- First the donor's header, copied whole, then one comment: the donor's path,
  the commit that it follows, what the file does not follow. Then
  `From SimplifyPort Require Import Port_monad.` (the kit),
  `From SimplifyPort.decl Require Import Simplify_import.` (the compiler's
  short module names: `DA`, `UA`, `T`, ...) and `From SimplifyPort.decl
  Require` (without `Import`) of each other module that the file names;
  never of the file's own module.
- The compiler's definitions in the compiler's ORDER, each under its NAME,
  with its arguments' names; before each, a comment with the donor's lines
  (`(* 19-29 *)`). The donor's comments that say WHY stay at their places
  (one that begins `CR` may be left out).
- Arguments are BY PLACE: no labels, in the order of the `.mli` (of the
  definition, if the function is not exported); the check compiles with
  `-nolabels`. HUMAN: the extracted definitions have no labels.
- Everything that the file calls is declared in `decl/` (search
  `decl/INDEX.tsv`; `decl/README.md` has the form), also the other files of
  Simplify: port against the declarations, never against another ported
  file. If a declaration is missing or wrong, declare the thing in your own
  file in the form of `decl/`, marked `PORT-GAP(decl)`, and tell the lead;
  never edit `decl/`.

## 2. Four ways to write OCaml's `let` and `;`

Every function, declared or ported, local or callback, has its result in
`M`. A call stands at the END of a function or branch, or is bound:

| Rocq | for | extracted |
|---|---|---|
| `let* x := f a in k` | `let x = f a in k`, the right side a CALL (also `let* '(a, b) :=`, `let* _ :=`) | `let x = f a in k` |
| `let& x := v in k` | `let x = v in k`, the right side a VALUE: a constant, a constructor, a local `fun` | `let x = v in k` |
| `e ;; k` | `e; k` (`e` of type `M unit`) | `let () = e in k` |
| `let! tmp1 := g x in f tmp1` | a call INSIDE another call: `f (g x)` | `f (g x)` |

`let!`: name each inner call `tmp1`, `tmp2`, ... (only these names), in THE
ORDER IN WHICH OCAML EVALUATES: the LAST argument first (right to left, in
the order of the Rocq arguments), inside each argument the same:

    let! tmp1 := h y in
    let! tmp2 := g x in
    f tmp2 tmp1                                  (* extracted: f (g x) (h y) *)

A `tmpN` is used EXACTLY ONCE, by the expression that follows its `let!`
directly, and not inside a `fun` or a branch of it: Rocq writes the call
where the `tmpN` is, so an unused one would vanish and one under a `fun`
would move. `make` only COUNTS WORDS (`tools/lint.py`): after its `let!`,
the word `tmpN` must stand once before the next `let! tmpN`; so do not bind
a `tmpN` again before it is used, and give no other variable that name. The
scrutinee of a `match` or `if` that is a call is a `let!` before it; BUT in
a match on several values (`match a, f x with`) the call is a `let*`: as a
`let!` Rocq moves it into the cases of `a` and DROPS it in a case that does
not look at it. A value at the end is `ret v`. Never: a call as an argument; Rocq's own `let x := f a in`; a
`Definition x : M T` without arguments; a computation in a pair, a list or a
record, or passed as an argument (but `or_else`, `and_then`). `a |> f b` is
`f b a`.

THE ORDER IS A FACT, by the human's word: "evaluation order in an oxcaml
compiler should always be right-to-left. Any occurrence otherwise in the
compiler is a bug. Note that record field order is unspecified in oxcaml
right now." So: right to left for the arguments of an application, of a
constructor and of a tuple. A RECORD (also an inline record) that has calls
in MORE THAN ONE field: the port takes the fields in the order of the TYPE,
the last field first, binds each call by `let*` (NOT `let!`: Rocq would put
the calls back inside the record, where OCaml's order is not fixed), and
the place is marked `PORT-GAP(record-order)`; a record with a call in at
most one field needs no mark. A place of the
compiler whose result depends on another order than right to left, or on
the order of the fields of a record: tell the lead (it is a suspected bug
of the compiler, for the human).

A function OF THE FILE applied to its first arguments only (`let simplifier
= simplify_x a b in`) is a value in both builds: `let&`, no mark.

PARTIAL APPLICATION of a declared function (`~f:(Acc.exit_continuation k)`):
`let! tmp1 := papp1 Acc.exit_continuation k in` (also `papp2`..`papp4`),
marked `PORT-GAP(papp)`, or write the `fun`. HUMAN: the port ASSUMES of every
declared function that it does nothing until it has all the arguments of
its interface. A ported recursive function passed as a value
(`~simplify_expr`) is `papp1 simplify_expr fuel`, without a mark.

| OCaml | Rocq |
|---|---|
| `match f x with ...` | `let! tmp1 := f x in match tmp1 with ... end` |
| `if c then e` (no `else`) | `(if c then e else ret tt) ;; k` |
| `a \|\| f x`, `a && f x` | `or_else a (f x)`, `and_then a (f x)`; of values: `\|\|`, `&&` |
| `x = y`, `<>`, `<`, `+` on integers; `not` | `x =? y`, `<>?`, `<?`, `+` (`Z`); `negb` |
| a literal integer other than 0 and 1 | `i2` .. `i10`, `i16`; else `Definition i255 : int := 255.` with `Extract Inlined Constant i255 => "255".` |
| `Misc.fatal_errorf "..%a.." p x` | `fatal_errorf2 "..%a.." p x` (the number of arguments; join the lines of the string) |
| `Format.fprintf ppf "..." a` | `Format.fprintf1 ppf "..." a` |
| `assert e`; `assert false` | `(let! tmp1 := e in assert_ tmp1) ;; k`; `assert_false` |
| `raise E`; `raise (E v)` | `raise_ M.E tt`; `raise_ M.E v` |
| `try e with E -> h` | `try_with (fun _ => e) M.E (fun _ => h)` |
| `match e with exception E -> h \| x -> k` | `match_exn (fun _ => e) M.E (fun _ => h) (fun x => k)` |
| `ref v`, `!r`, `r := v`; `lazy e`, `Lazy.force l` | `mk_ref v`, `get r`, `set r v`; `lazy_ (fun _ => e)`, `force l` |
| `while c do b done` | `while_ (fun _ => c) (fun _ => b)` |
| `x == y`, `compare x y`, `x = y` not on integers | `phys_equal x y`, `poly_compare x y`, `poly_equal x y` (calls) |
| `a / b`, `a mod b` on integers | `int_div a b`, `int_mod a b` (calls: they may raise) |
| `E v` as a value (`raise_with_backtrace E bt`) | `exn_make M.E v` |
| `f ?opt:None x`, `f ~opt:v x` (optional argument) | `f None x`, `f (Some v) x` by place |
| `p when c -> e` | the pattern, then `if c then e else` the other cases; a `c` of constants and parameters only may be a second scrutinee (`match x, c with p, true => e`), marked loose |

## 3. Recursion

A recursion that Rocq sees to end (on a list): a plain `Fixpoint`. Any other:
`fuel` is the FIRST parameter, and the function is

    Fixpoint f (fuel : fuel) ... {struct fuel} : M R := recursive! fuel in BODY

Every recursive call in BODY, or use as a value, takes `fuel`. Mutual
recursion: `with`. A local `let rec`: Rocq's own `let f := fix f (fuel :
Port_monad.fuel) ... := recursive! fuel in ... in` (not `let&`). A caller
outside the recursion: `let_fuel! fuel in f fuel ...`. In the identity build
the fuel is a proposition, which the extraction erases: the extracted code
is the compiler's `let rec`. HUMAN: there is no axiom in the real build; a
statement of Rocq about a function can only be about runs for which the
fuel was enough, and that it holds of the OCAML code is NOT established now
(section 7).

## 4. Types

- A VARIANT of `decl/` has the compiler's constructors; one with an inline
  record takes the fields BY PLACE: `Closure_info.Closure code_id _ _ _ _`.
  Write the `match` as the compiler does. Rocq prints the constructors by
  their full names; a match on a variant that has an inline record is
  printed as the application of one function for each constructor (section
  7), and a case `_` as one function for each constructor that is left.
- A RECORD of `decl/` has the compiler's fields: `{| S.simples := a;
  S.simple_tys := b |}` in terms and patterns; all the fields for `{ r with
  f = v }`. A field is read with the module's OWN name,
  `r.(Simplify_simple.simples)`: through a short name (`r.(S.simples)`) Rocq
  prints the call `S.simples r`, which OCaml refuses. A mutable field is set
  by `M.set_f r v`.
- What `decl/` marks `PORT-GAP(type)` (a GADT, a few records): its makers
  `mk_C` and its eliminator `match_T`, as `decl/` says.
- A type that the file itself DEFINES: a Rocq `Inductive` or `Record` with
  the compiler's names, if it is a plain variant or record (Rocq prints the
  OCaml definition, and one function for each field of a record: a function
  of the file that only reads the field of its name IS that projection;
  mark it `PORT-GAP(loose)`). Else (inline record, GADT, mutable field,
  polymorphic variant, a field named `unit` or another name that the
  extraction changes): mark `PORT-GAP(type)` and either the OCaml
  definition verbatim (below) with, in Rocq, what `decl/` has for it copied
  into the file; or, to keep the definition at its place (inside a module
  of the file), the Rocq type under the name `t_` with its `Extract
  Inductive t_ => "t" [...]`, then `Definition t : Type := t_.` and `Extract
  Constant t => "| A | B of { x : int }".`: Rocq prints `type t = ` and
  that text.
- OCaml text that must be in the extracted file as it is (`open!`, such a
  type, `exception E`, a functor application, a wrapper with an optional
  argument) goes between a line `(*OCAML` and a line `OCAML*)` (copied to
  the head of the extracted file) or `(*OCAML-END` and `OCAML-END*)` (to its
  end). Mark it `PORT-GAP(verbatim)` unless it is an `open`.
- An exception of the file: `exception E` verbatim, `Parameter E : exception
  unit.` and `Extract Inlined Constant E => "((fun () -> E), (function E ->
  Some () | _ -> None))".`
- A module that the file makes with a functor (`module SCC =
  Strongly_connected_components.Make (...)`): the OCaml line verbatim, and
  `From SimplifyPort.decl Require Import Foo__local.`, which declares it
  (`decl/README.md` lists the seven files that have one).
- A ported function with an OPTIONAL parameter: `(x : option T)` by place,
  and at the end `(*OCAML-END let f ?x a = f x a OCAML-END*)`.
- One name space: where a type of the file has the name of a function or a
  field, the TYPE gets one `_` after it; a name that is a word of Rocq gets
  one too (`exists_`). Where a parameter is named `t`, write the type
  `Foo.t`; where a variable has the name of a type, give its type by a cast
  after the `fun`, not in the binder.
- A donor that does not `open! Simplify_import` does not import
  `decl/Simplify_import` either: its own `module X = Y` lines are `Module X
  := Y.`, its `open! Flambda.Import` is `Import Flambda.Import_.` For `@` on
  lists add `Local Open Scope list_scope.` after the two scopes. A function
  that takes two pairs apart: name them and write `let* '(a, b) := ret pat
  in`. A `\n` in a format string is a real line break in the Rocq string.

## 5. Gaps: never hidden

A comment that BEGINS `(* PORT-GAP(kind): words *)`, at the place. The kinds:
`unported` (a function left as a parameter: the mark, `Parameter f : ... ->
M r.` and `Extract Constant f => "fun _ -> Misc.fatal_error
""PORT-GAP(unported): f""".`); `partial` (part of a body replaced by
`fatal_error "PORT-GAP(partial): ..."`); `loose` (ported, but not line
beside line: say what differs; an attribute such as `[@inline]` that is not
kept); `order` (you are not sure of the order of evaluation); `type`;
`verbatim`; `papp`; `record-order` (section 2); `init` (a top-level value that the compiler computes
with effects when the module starts: a `Parameter`, its OCaml text
verbatim, and `Extract Inlined Constant x => "x".`); `decl`. Prefer a marked
gap now to a long fight: the first version is for the structure.

## 6. The work

    # rocq, ocamlc.opt and ocamlformat 0.29.0 on the PATH;
    # CMI_ROOT: the _build/default of a dune build of the compiler
    make CMI_ROOT=ROOT extracted/DIR/foo.ml          # one file
    make CMI_ROOT=ROOT _build/check/DIR/foo.status   # its types

One process; no `-j`. A file is committed when both builds of Rocq compile
it AND `extracted/DIR/foo.ml` type-checks (`overlay` is enough: the
compiler's module with your definitions in the place of its own has the
compiler's interface; `strict`: your file has the whole interface). One
commit a file: the `.v` and its `extracted/` file, nothing else. Read your
extracted file beside the donor before you commit: that reading is the
review. If OCaml says `Unbound record field`, `This form is not allowed as
the type of the inlined record could escape`, or a name is not the
compiler's, the cause is in section 7.

## 7. What Rocq's text looks like, and known problems to look at later

WHERE THE EXTRACTED TEXT IS NOT THE COMPILER'S (directives alone cannot):
no labels; `let () = e in` for `e;`; a variable that is bound again gets a
number (`dacc0`, `dacc1`), also one with the name of a field or type of an
opened module; the short names of Simplify_import are written out
(`Downwards_acc.denv`); the cases of a match are in the order of the type;
`a :: []` for `[a]`; an optional argument is the applied text `(fun x__1
x__2 -> F.f ?l:x__1 x__2) None a`; a match on a variant with an inline
record, and the building of such a constructor, are applied functions (`(fun
f__1 f__2 x__0 -> match x__0 with ...) (fun a -> ...) (fun b -> ...) x`);
in EVERY match the body of a case with several patterns, or of `_`, is
written once for each constructor that it stands for (a `_` over a type of
30 constructors is 30 cases); a record that the file defines brings one
function for each field (`let name i = i.name`); Rocq's `open` lines come
AFTER the verbatim head, so a name of the head that an opened module also
has is hidden from the rest of the file (do not write a bare `t` in a
string of `Extract Inductive`);
`try`, `match .. with exception`, `while` are calls of `Port_monad`
(`runtime/port_monad.ml`), `lazy e` is `Lazy.from_fun`; a local function is
`let f = fun x -> ...`; each definition has a comment `(** val f : ... **)`
with its Rocq type, and the file begins with `open` lines for the modules
of `decl/` whose records it uses.

KNOWN PROBLEMS OF THE EXTRACTION (the human has put them off; none is
checked by a tool, but the first in part). In the identity build `M A` is `A`, and
Rocq's extraction takes every term for a pure one:
1. A `let!` that is not used is DROPPED with its call (also one that is the
   second value of a `match a, tmp1 with`, in the cases of `a` that do not
   look at it); used twice it stays a `let`; used under a `fun` or in a
   branch the call MOVES there
   (`let! tmp1 := f x in g (fun y => h tmp1 y)` gives `g (fun y -> h (f x)
   y)`). `make` counts the words only: it does not know scopes or
   shadowing, and it does not look at branches or `fun`s.
2. Rocq's own `let x := f a in k` with `x` used once: the call moves to the
   use; not used: dropped. (Hence `let*`, which is a match and stays.)
3. A computation that is STORED (in a pair, a record, a variable, a
   top-level definition without arguments) is run when it is built and
   once, not where and as often as the real build says.
4. ETA: `fun x => f a x` may be printed `f a`; if OCaml's `f` acts when it
   has `a` only, the effect moves. The same assumption as for `papp`.
5. A function that returns a proposition or a type is erased with its call
   (`let* _ := (f x : M True)`).
6. The realisation strings of `decl/` are texts: a string that is not a
   function or constructor (a call) would run wherever Rocq puts it.
7. A variable named `program_branch_N` that is used once may be inlined
   even where an ordinary `let` is kept. Do not use `Program`. And
   `Extraction Inline f` puts the arguments of `f` where its body uses
   them, whatever the flags: with `Definition two (a b : M int) := ...`
   inlined, `two (tick 1) (tick 2)` may run the ticks in another order or
   twice. No ported file has an `Extraction Inline`; the kit has it for
   `ret` and `papp1` .. `papp4` only.
8. The identity build is NOT a model: its `fatal_error : forall A, string ->
   A` is a parameter, its fuel never ends. Nothing is proved in it;
   statements are about `monad/real`. That the extracted OCaml does what
   `monad/real` says is not established: it needs enough fuel, the order
   of evaluation that the human states, the assumption on partial
   application, AND an answer to the problems 1 to 7.
9. `int` is `Z`: no overflow in Rocq. Physical equality and the contents of
   references are parameters; the printing of a fatal error is not modelled.
