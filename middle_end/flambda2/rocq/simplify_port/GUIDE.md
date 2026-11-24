# The port of Simplify to Rocq: the guide for a porter

`simplify/DIR/foo.ml` of the compiler becomes `simplify_port/DIR/Foo.v`. `make`
compiles it, extracts it, removes the monad (`tools/unmonad`), formats it
and checks its types: the result is `extracted/DIR/foo.ml`, which is
committed and should read like the compiler's file. `Simplify_expr.v` and
`Simplify_apply_cont_expr.v` are the models: read them beside their donors.
Points marked HUMAN are the human's to judge.

## 1. The file

- First the donor's header, copied whole, then one comment: the donor's path,
  the commit that it follows, what the file does not follow. Then
  `From SimplifyPort Require Import Port_monad Simplify_import.` (the kit and
  the compiler's short module names: `DA`, `UA`, `T`, ...), then
  `From SimplifyPort.decl Require` of each other module that it calls.
- The compiler's definitions in the compiler's ORDER, each under its NAME,
  with its arguments' names; before each, a comment with the donor's lines
  (`(* 19-29 *)`). Rocq has ONE name space: where a type or a field has the
  name of a function, the TYPE or the FIELD gets one `_` after it (the tool
  takes it off); so does a name that is a word of Rocq (`exists_`). Where a
  parameter is named `t`, write the type `Foo.t` (the file's own name).
- Arguments are by place: labels are dropped, in the order of the `.mli`
  (of the definition, if the function is not exported). The check compiles
  with `-nolabels`. An optional parameter `?x` is `x__opt : option T`.
  HUMAN: the extracted definitions have no labels yet.
- Everything that the file calls is declared in `decl/` (search
  `decl/INDEX.tsv`), also the other files of Simplify: port against the
  declarations, never against another ported file. If a declaration is
  missing or wrong, declare it in your own file, in the form of `decl/`,
  marked `PORT-GAP(decl)`; never edit `decl/`.

## 2. The one rule: every call is bound

Every function, declared or ported, local or callback, has its result in
`M`. So a call can stand in two places only: at the END of a function or
branch, or on the right of `let*`:

    let* denv := DA.denv dacc in                 (* let denv = DA.denv dacc in *)
    let* dbg := DE.add_inlined_debuginfo denv dbg in

The arguments of a call are VALUES: variables, constants, constructors and
tuples of values, `fun`. A value at the end is `ret v`. `e1; e2` is
`e1 ;; e2`. Never: a call as an argument; `let x := f a in` (a plain `let`
of a call); a `Definition x : M T` without arguments; a computation in a
pair, a list or a record; a `fun` whose body is not in `M`. The tool refuses
all of these (section 3), so follow its message.

NESTED CALLS. The compiler writes `f (g x) (h y)`. Name each inner call
`tmp1`, `tmp2`, ... (only these names) and bind them in THE ORDER IN WHICH
OCAML EVALUATES: the LAST argument first (right to left, in the order of the
Rocq arguments), inside each argument the same:

    let* tmp1 := h y in
    let* tmp2 := g x in
    f tmp2 tmp1                                  (* extracted: f (g x) (h y) *)

The tool puts a `tmpN` back inside the call when that keeps the order; if
your order is not right-to-left a `let tmpN` stays in the extracted file,
which shows it. `a |> f b` is `f b a`. `a && b`, `a || b` with a call in `b`:
`if a then b else ret false`, `if a then ret true else b` (the tool writes
`&&`, `||` again). HUMAN: OCaml leaves the order of evaluation of arguments
unspecified; the port fixes right-to-left, which is what ocamlopt does.

PARTIAL APPLICATION (`~f:(Acc.exit_continuation k)`, `~simplify_expr`):
`let* tmp1 := papp1 Acc.exit_continuation k in` (also `papp2`..`papp4`), or
write the `fun`. HUMAN: the port assumes of every declared function that it
does nothing until it has all the arguments of its interface.

| OCaml | Rocq | 
|---|---|
| `let x = e in k` | `let* x := e in k` (pure `e`: `let x := e in k`) |
| `let a, b = e in k`; triples | `let* '(a, b) := e in k`; `'(T3 a b c)` |
| `match f x with ...` | `let* tmp1 := f x in match tmp1 with ... end` |
| `C { a; b }`, `{ r with f = v }` | `C a b` by place; all the fields, by the maker |
| `r.f`; `r.f <- v` | `M.f r` (pure); `M.set_f r v` |
| `Misc.fatal_errorf "..%a.." p x` | `fatal_errorf "..%a.." (fmt: p; x)` (join the lines of the string) |
| `assert e`; `assert false` | `let* tmp1 := e in assert_ tmp1`; `assert_false` |
| `raise E`; `raise (E v)` | `raise_ M.E tt`; `raise_ M.E v` |
| `try e with E -> h` | `try_with (fun _ => e) M.E (fun _ => h)` |
| `match e with exception E -> h \| x -> k` | `match_exn (fun _ => e) M.E (fun _ => h) (fun x => k)` |
| `ref v`, `!r`, `r := v` | `mk_ref v`, `get r`, `set r v` (all bound) |
| `lazy e`, `Lazy.force l` | `lazy_ (fun _ => e)`, `force l` |
| `while c do b done` | `while_ (fun _ => c) (fun _ => b)` |
| `x = y` on integers, `+`, `not`, `&&` on values | `x =? y`, `+`, `negb`, `&&` (pure, `Z`) |
| `x == y`, `compare x y` | `phys_equal x y`, `poly_compare x y` (bound) |

## 3. Why the extracted code does what the Rocq code says

Rocq's extraction treats every term as pure: it may drop an unused value,
inline a `let`, move a term under a `fun`. The kit meets this in two steps.
(a) `bind`, `ret` and every operation are OPAQUE to the extraction (literal
strings): it cannot look inside a monadic step, so each step and its
continuation reach the tool as written. (b) `tools/unmonad` REFUSES a file
that is not in this fragment: a computation is a bind of a computation, a
`ret` of a value, a call on values, or a `match`/`if`/`let` on a value with
computations as branches; a value is never a call; a variable is never run.
For that fragment, writing `bind e (fun x -> k)` as `let x = e in k` gives
the direct-style program whose effects are those of the binds, in their
order, each once; nothing that the extraction may do to a VALUE can change
them. The realisations of declared things are closed lambdas applied to
values; reducing them is pure. So the discipline is checked on every file
at every `make`, on the very text that is rewritten. (c) What the syntax
cannot see, Rocq's types refuse: `M A` is an inductive type that only the
kit's operations make and run, so a function is never taken for a
computation, and `papp1` cannot apply a function to its last argument
(`tools/test/`). What is NOT modelled: the printing of a fatal error (a
parameter); the contents of references; physical equality (Rocq may share
or copy a value where the compiler's code does not).

## 4. Recursion

A recursion that Rocq sees to end (on a list): a plain `Fixpoint`. Any other:
`fuel` is the FIRST parameter, the function is a `Fixpoint ... {struct fuel}`

    match fuel with Out => out_of_fuel | More fuel => BODY end

and every recursive call in BODY, or use as a value (`papp1 simplify_expr
fuel`), takes the smaller `fuel`. Mutual recursion: `with`. A local `let
rec`: `let f := fix f (fuel : fuel) ... in`. A caller outside the recursion:
`let* fuel := get_fuel tt in`. Name it `fuel` only: the tool removes the
parameter, so the extracted code is the compiler's `let rec`. HUMAN: what
Rocq says of a function then holds of OCaml runs for which the fuel was
enough; there is no axiom.

## 5. Types, exceptions and other OCaml that Rocq cannot say

- A type that the file defines and that its `.mli` shows is in `decl/`
  already: use it from there. Define a type yourself only if it is abstract
  or absent in the `.mli`: a Rocq `Record` / `Inductive` with the compiler's
  names (Rocq extracts the OCaml type; write `r.(f)` or `f r` for a field,
  `{| f := v; ... |}` with all the fields for `{ r with f = v }`).
- OCaml text that must be in the extracted file as it is (`open!`, a type
  that Rocq cannot make, `exception E`, a functor application) goes between
  a line `(*OCAML` and a line `OCAML*)`; it is copied to the head of the
  extracted file. Mark it `PORT-GAP(verbatim)` unless it is an `open`.
- An exception of the file: `exception E` verbatim, and
  `Parameter E : exception unit.` with
  `Extract Inlined Constant E => "E".` (with an argument:
  `"(fun x__1 -> E x__1)"`).

## 6. Gaps: never hidden

A comment that BEGINS `(* PORT-GAP(kind): words *)`, at the place. The kinds:
`unported` (a function left as a parameter: the mark, then
`Parameter f : ... -> M r.` and nothing else; the extracted file gets
`let f _ = Misc.fatal_error "PORT-GAP(unported): f"`); `partial` (part of a
body replaced by `fatal_error "PORT-GAP(partial): ..."`); `loose` (ported,
but not line beside line: say what differs); `order` (you are not sure of
the order of evaluation); `type` (a type left abstract or bent); `verbatim`;
`init` (a top-level value that the compiler computes with effects when the
module starts: a `Parameter`, its OCaml text verbatim, and
`Extract Inlined Constant x => "x".`); `decl`. Prefer a marked gap now to a
long fight: the first version is for the structure.

## 7. The work

    # rocq, ocamlfind, ocamlc.opt and ocamlformat 0.29.0 on the PATH;
    # CMI_ROOT: the _build/default of a dune build of the compiler
    make CMI_ROOT=ROOT extracted/DIR/foo.ml          # one file
    make CMI_ROOT=ROOT _build/check/DIR/foo.status   # its types

One process; no `-j`. A file is committed when Rocq compiles it AND
`extracted/DIR/foo.ml` type-checks (`overlay` is enough: the compiler's
module with your definitions in the place of its own has the compiler's
interface; `strict`: your file has the whole interface). One commit a file:
the `.v` and its `extracted/` file, nothing else. Read your extracted file
beside the donor before you commit: that reading is the review.
