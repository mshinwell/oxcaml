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

- First the donor's header, copied whole (by a copy, not typed), then one
  comment: the donor's path, the commit that it follows, what the file does
  not follow. Then
  `From SimplifyPort Require Import Port_monad.` (the kit),
  `From SimplifyPort.decl Require Import Simplify_import.` (the compiler's
  short module names: `DA`, `UA`, `T`, ...) and `From SimplifyPort.decl
  Require` (without `Import`) of each other module that the file names;
  never of the file's own module.
- NAMES OF OTHER MODULES: write each as the compiler's file writes it at
  that place, with the short module name (`DA.denv`, `T.meet`, `AC.args`)
  or whole (`Downwards_acc.denv`). The extracted file prints it as you
  wrote it (section 7, ABBREVIATIONS). The short names that the compiler's
  file makes itself (`module U = Unboxing_types`) are a Rocq library of
  the file's own, `abbrev/FILE/Port_abbreviations.v` (FILE in small
  letters; it holds `Module U := Unboxing_types.` and the `Require`s that
  it needs), which the file takes by `From SimplifyPort.abbrev.FILE Require
  Import Port_abbreviations.`; and the compiler's own lines stand in the
  OCaml head of the file, in the compiler's order (`make` stops if a line
  of the head and a line of the library do not name the same module).
- The compiler's definitions in the compiler's ORDER, each under its NAME,
  with its arguments' names; before each, a comment with the donor's lines
  (`(* 19-29 *)`): THE NOTE OF LINES. It is ONE range, from the first line
  of the donor's definition of that name to its last (not its first lines
  only); words may follow a full stop (`(* 19-29. Words. *)`; a colon
  there makes it a plain comment). For things that the donor defines
  together (`let rec f .. and g ..`), the lines of the one, or of all
  together. `make lines` (`tools/lines.py`, a part of `make check`)
  compares the note before each `Definition`, `Fixpoint`, `Inductive`,
  `Record` and `Module` with the lines that the donor's typed tree has
  for the thing of that name and kind in that module
  (`decl/DONOR-ITEMS.tsv`), as tokens, so that lines of comment at either
  end are free; a definition that the donor has and that has no note is
  an error. The note counts for all the sentences of its group (an
  `Inductive t_` and the `Definition t` after it). `Module X := ..`
  sentences that follow one another may have one note, the lines of all
  of them (the donor has nothing else between them). A CLAUSE of a
  `Fixpoint`, `with f (..`, is written AT THE MARGIN of its `Fixpoint`
  and has its own note directly before it (a mark may stand between):
  the lines of the donor's `and f ..`, not those of the whole `let rec`.
  `make lines` compares it as it does the note of a definition, and a
  clause without a note is an error. NOT JUDGED, and listed by
  `LINES_ALL=1 make lines`: a definition in a functor or a module type
  of the file; a name that the donor does not have (a helper); a
  `Definition` whose text a directive gives (`make given`).
- A note INSIDE a definition names WHOLE LINES of the part that the Rocq
  text after it follows, from the line where the part begins to the line
  where it ends (parts that follow one another: from the first line of
  the first to the last line of the last). A `let .. in` goes from the
  line of its `let` to the line of its `in`, also when the `in` stands
  alone on its line; an arm of a match is named with the lines of its
  pattern, or its body alone. A comment that speaks of one piece of the
  text (`(* 12: words *)`: a pattern, the parameters of a function, one
  argument) names the lines where that piece stands. `make lines` checks
  a note inside a definition (the note of a clause is not one) ONLY to
  lie inside the lines of its item. Whether it begins and ends where a
  part does is checked by NO TOOL: when `tools/lines.py` was written,
  every note inside was read once by hand against the donor (the Rocq
  line after it against the two ends of its range), and so were the
  lines that the marks name. Nothing repeats that reading.
- The donor's COMMENTS stay at their places, in the donor's words (one
  that begins `CR` may be left out): `make comments` lists the ones that
  are missing and the headers that differ.
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
not look at it. A value at the end is `ret v`. Never: a call as an
argument; Rocq's own `let x := f a in`; a `Definition x : M T` without
arguments; a computation in a pair, a list or a record, or passed as an
argument (but `or_else`, `and_then`). `a |> f b` is `f b a`.

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
`let! tmp1 := papp1 Acc.exit_continuation k in` (also `papp2`..`papp4`), or
write the `fun`. In OCaml a function runs nothing while it has FEWER
ARGUMENTS THAN THE FIRST GROUP OF PARAMETERS OF ITS DEFINITION: the
parameters that the definition writes together (`let f a b = ..`), and the
cases of a `function` directly after them. A function that is the whole
body of another (`let f a = fun b -> ..`) is a second group; it counts only
if every parameter before it is a variable or `_` without a default, since
OCaml matches a pattern and computes a default as soon as the first group
is full (`decl/README.md`, last section, "The count"). The interface does
not say this number: the interface of `Typing_env.resolver` shows two
arguments, and its definition
(middle_end/flambda2/types/env/typing_env.ml:337) has one parameter and
reads a field, so it runs when it has the first. `decl/ARITIES.tsv` has the
number for each declared value, read from the compiler's typed trees, and
`tools/lint.py` checks each `pappN F` against it (`tools/papp.py` says how,
and what it does not see). Write `pappN` plain and the function as a name
(`papp1 M.f a`): the lint refuses `Port_monad.papp1`, `@papp1`, and a
function that is not a name. Write a declared function with its module: a
name without a module that the lint finds under an `Import` does not pass
if the name also stands anywhere in the file where a variable may be bound.
A use that passes has NO mark. A use that does
not pass (the first group has no more parameters than the use gives
arguments; or no definition was read; or the
function is a variable, of which nothing is known) has, before it in the
same definition, the mark `(* PORT-GAP(papp): [F] ... *)`: the function in
square brackets as the use writes it, nothing else in square brackets, and
what runs at the use (or that the definition was not read), in the port's
own words and with the place, not with a line of the compiler. The lint
prints each use that keeps its mark; a use that needs a mark and has none,
and a mark that is not needed, are errors. A partial application WITHOUT
`pappN` (a definition that is one: `Definition g : .. := M.f a.`): put the
same mark and run the lint, which then counts the arguments as words; take
the mark off if the lint says that it needs none. Without a mark the lint
does not see such a place. `make papp` (a part of `make check`) is a second
step after the lint, and no check by itself: for each use that the lint
passes of a function of a ported file of Simplify, it looks for the
definition in `extracted/`, in the module where the compiler has it, and
wants more parameters there too; what it does not find there is an error.
A FUNCTION OF THE STANDARD LIBRARY (`papp1 Option.map f`): `decl/ARITIES.tsv`
has no number for it. The lint leaves such a use to `make papp`, which
reads the tree's own `stdlib/`, as words, and wants more parameters in the
definition there than the use gives arguments: then the use has no mark.
It looks only for a value of a unit of the library itself (`List.map` in
`stdlib/list.ml`; not for what `Set.Make` or `Map.Make` makes), and counts
only parameters that are plain names; any other use keeps the mark, with
what `make papp` says of it. THE LIMIT: a compiler of the first stage is
linked with the standard library of the compiler that builds it. That
library is not of this repository, and no tool here reads a definition of
it: such a mark goes on the reading of the tree's own library only.
A FUNCTION OF THE FILE that is given its first arguments by `pappN` (a
ported recursive function passed as a value, `~simplify_expr`, is `papp1
simplify_expr fuel`) is checked by `make papp`, not by the lint: the
definition in the file's own extracted text, in the module where the file
binds the name by `Definition`, `Fixpoint` or `with`, must have more
parameters than the use gives arguments. The fuel counts as an argument
here, though the extraction erases it: that only makes the rule stricter.
A LOCAL FUNCTION (a local `let rec`, section 3) that is given its first
arguments by `pappN` is checked by `make papp` too, in ONE shape and by
uniqueness, since the tool follows no scope: the file has one `let f`, it
is `let f := fix f (binders) .. := .. in`, no other thing of the file has
the name f, and the use stands in the same `Definition` or `Fixpoint` D,
inside the `fix` or after its `in`; the extracted definition of D has one
line `let rec f` inside it, with more parameters than the use gives
arguments. The rules below hold for it with the head of the `fix`.
A use that `make papp` cannot pass has the mark, which says what the
extracted text has: a local function that is not read so (bound by `fun`,
or twice); a definition that is another name or an application; a
function inside a functor; a function with no more parameters than it is
given. `make papp` IS NO ELABORATOR AND NO RESOLVER OF ROCQ'S NAMES: it
reads words, counts the head of the binding as it is written, and accepts
nothing that Rocq could have completed. So it also refuses the use, so
that it needs the mark, unless the words show that the OCaml use gives no
more arguments than are written, and which function is meant. Write such
a function so:
- it and its use stand outside any `Section` (after a section Rocq gives
  the function the section's variables as arguments);
- the head of its binding, from the name to `:=`, writes every parameter
  that the use gives and at least one more, each as `(names : type)` or a
  plain name, and has no brace but `{struct x}`, no square bracket, no
  backquote and no number anywhere; its types, and the type of the result
  if it writes one, are made of names, round brackets, `->`, `*`, commas
  and colons (an implicit parameter can hide in the type of the result:
  `: forall {n : nat}, ..`);
- its body is no `fun` and no `fix`, also after `let`s (a `fun {n : nat}`
  there is an implicit parameter too);
- every sentence of the file begins with one of the words that
  `tools/papp.py` lists (`Definition`, `Fixpoint`, `Inductive`, `Record`,
  `Parameter`, `Module`, `End`, `From`, `Import`, `Extract`, `Local Open
  Scope`, and a few more): no `Set Implicit Arguments`, no `Arguments` of
  the function, no `Notation`, no attribute, no proof;
- the use stands after the binding, or in its sentence, with no `Import`
  or `Require` between them, and not outside the module of the binding;
- its name is not used for a variable anywhere in the file (a parameter, a
  `let`, a pattern, a field of a record).
A use that `make papp` passes has been checked only under these shapes;
`tools/papp.py` lists what it does NOT establish (the term that Rocq
elaborates is not looked at; a coercion, a notation of the kit, or any
mechanism that the tool does not know is not implied safe). `make papp`
prints each such mark that stays, and a mark
that is not needed is an error there. The mark of a function of the file
stands before a `pappN` of it: without `pappN` a function of the file that
is given its first arguments is a `let&` value with no mark (above), and
the lint does not read such a place through a mark as it does for a
declared function.

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
- A RECORD of `decl/` has the compiler's fields: `{| Simplify_simple.simples
  := a; Simplify_simple.simple_tys := b |}` in terms and patterns. Write a
  field with the module's OWN name,
  not a short name of Simplify_import: `r.(S.simples)` is printed as the
  call `S.simples r`, which OCaml refuses. And a record that is TAKEN APART
  must have its TYPE by the module's own name where the value comes from
  (the binder `(x : Simplified_expr.simplified_apply_)`, the call
  `Simplify_simple.simplify_simples`): Rocq prints the fields of the
  pattern under the name by which the type was written, and through a
  short name that is `Simplify_import.SE.apply`. A mutable field is set by
  `M.set_f r v`.
- A RECORD UPDATE `{ t with f = v }` is a SETTER of the file, defined once
  for each set of fields that the file updates, before its first use:

      (* 12, 40 and 57-59. [{ t with typing_env }] *)
      Definition update_typing_env (t : Downwards_env.t)
          (typing_env : TE.t) : Downwards_env.t :=
        {| round := t.(round); typing_env := typing_env; ... |}.
      Extract Inlined Constant update_typing_env =>
        "(fun t typing_env -> { t with typing_env = typing_env })".

  and `update_typing_env t v` at each place (a VALUE: `ret (update_.. t
  v)`, `let& t := update_.. t v in`). The Definition says in Rocq what the
  update is, with ALL the fields; the text is what OCaml reads, in exactly
  this form (`t`, then one parameter for each field, with the field's
  name, in the order of the compiler's text; `update_f_g` for two
  fields). Rocq does not compare the two:
  `tools/lint.py` does, as words (each field of the text is given its
  parameter, every other field is `g := t.(g)`). THE NOTE before the
  Definition names EVERY place of the compiler's file where a record
  update of that type gives exactly these fields, in this order: the line
  where the update begins, or its lines (`57-59`). `make given` checks the
  note both ways against `decl/UPDATES.tsv` (each place that is named is
  such an update, and each such update is named), and that the record of
  the Definition has the fields of the compiler's type in the order of
  the type. A field whose new value is a call: `let!` before the setter if
  it is the only one, else `let*` each (section 2, records).
- What `decl/` marks `PORT-GAP(type)` (a GADT, a few records): its makers
  `mk_C` and its eliminator `match_T`, as `decl/` says.
- A COERCION of a private abbreviation (`(x :> int)`, where `x` is a name
  of the type `M.t`, which is `private int`): the pure function that
  `decl/` declares after the type, `M.coerce_t_to_int x`. `decl/` has one
  for each such coercion that the files of Simplify write of a name; do
  not declare it in the file.
- A type that the file itself DEFINES: a Rocq `Inductive` or `Record` with
  the compiler's names, if it is a plain variant or record (Rocq prints the
  OCaml definition, and one function for each field of a record: a function
  of the file that only reads the field of its name IS that projection;
  mark it `PORT-GAP(loose)`). Else (inline record, GADT, mutable field,
  polymorphic variant, a field named `unit` or another name that the
  extraction changes): either the OCaml definition verbatim (below) with,
  in Rocq, what `decl/` has for it copied into the file; or, to keep the
  definition at its place (inside a module
  of the file), the Rocq type under the name `t_` with its `Extract
  Inductive t_ => "t" [...]`, then `Definition t : Type := t_.` and `Extract
  Constant t => "| A | B of { x : int }".`: Rocq prints `type t = ` and
  that text. Before it, the note of the lines of the compiler's
  definition. The strings of `Extract Inductive` are THE FORM of `decl/`
  for that definition, and no other text (`x__1 ..` for the arguments,
  `f__1 ..` for the cases, `x__0` for the value; the header of
  `tools/given.py`, R3, has it in full): `make given` makes the form again
  from the OCaml definition that the file gives, compares, and counts the
  arguments of the Rocq constructors. Mark `PORT-GAP(type)` only what it
  cannot check, and say why: a type that is written out in the directive
  (polymorphic variants, a tuple with labels); a definition that is not
  the compiler's text as it stands (the types of a recursive group in
  another order); functions that are written for the file (the maker and
  the accessors of a record with a mutable field).
- OCaml text that must be in the extracted file as it is (`open!`, such a
  type, `exception E`, a functor application, a wrapper with an optional
  argument) goes between a line `(*OCAML` and a line `OCAML*)` (copied to
  the head of the extracted file) or `(*OCAML-END` and `OCAML-END*)` (to its
  end). Before it, the note of the compiler's lines that it is: `(* 17 *)`,
  `(* 18-23 and 43 *)`; with words after a full stop if it does not stand
  where the compiler has it (`(* 120. The exception stands at the head of
  the extracted file. *)`). Mark it `PORT-GAP(verbatim)` only if it is NOT
  the compiler's lines (a wrapper, text that the port itself needs), and
  say why.
- GIVEN TEXT. A block and the strings of a directive (`Extract Constant`,
  `Extract Inlined Constant`, `Extract Inductive`; write no other
  directive) are OCaml that Rocq copies and does not read. `make given`
  (`tools/given.py`, a part of `make check`) compares each of them with
  the compiler's file, as tokens. A text is the compiler's LINES that the
  note before it names (a block; the text of `Extract Constant`, which
  holds what follows `type t =` or `let x =`); or a SETTER (above); or THE
  FORM of a type whose definition the file gives (above); or the
  constant's own name, the pair of an exception, a number (any one
  number of OCaml: `32`, `0x1F`, `0.`, `1e3`, `(-1)`; an integer is that of
  the Rocq `Definition`; for a `Parameter`, as for every float, a literal
  of the compiler's lines that the note names). A NOTE OF LINES is a comment that begins with the
  lines, `(* 12-20 *)`, `(* 12-20 and 43. Words. *)`; it stands before the
  text, and only comments and sentences without a body (`Parameter`,
  `Inductive`, `Record`, the `Definition` of the directive) stand
  between. A text that is none of these needs a mark over it:
  `verbatim`, `type`, `update`, `init`, `decl` or `unported` (section 5).
  A mark `verbatim`, `type` or `update` is an error if EVERY text under it
  holds one of these (the mark is not needed: a note of lines is enough);
  a mark `init`, `decl` or `unported` may stay over text that holds.
  `GIVEN_ALL=1 make given` prints one line for each text: what holds, and
  by which of the differences that are allowed. The header of the tool
  says what it does NOT establish: above all, that the ported code USES
  the setter, the maker or the number where the compiler has the update,
  the construction or the number.
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

- FORMS THAT PORTED FILES USE; read the file. A record with a mutable
  field (the type abstract, a maker, a getter and a setter in `M`):
  `Rebuilt_static_const.v`. Several types of one file with the same
  constructors (`Invalid`, `Invalid_`, `Invalid__`, each told its OCaml
  name): `Expr_builder.v`. A functor of the file: a Rocq `Module` with a
  `Section` whose variables are the functor's members
  (`Simplify_unary_primitive.v`), or a function of those members
  (`flow/Data_flow_graph.v`), or a Rocq functor over a module type of
  `decl/` (`Simplify_binary_primitive.v`). Polymorphic variants:
  `env/Downwards_env.v`.
- INSIDE A ROCQ FUNCTOR (facts found by trying): a directive on a
  `Parameter` of the body is not honoured, and Rocq says nothing; a module
  of `decl/` that the body names through an alias (`Module R :=
  Target_ocaml_int.`) loses its directives there (Rocq prints
  `R.Set_.cardinal`), and its value names get in the way of local
  variables (`machine_width0`): give it to the body through an identity
  functor of its module type, as `Simplify_binary_primitive.v` does. A
  module cannot be named `Set` in Rocq: `decl/` says `Set_`, and where
  Rocq must print that name (under a functor's parameter) an OCaml head
  gives the compiler's modules the name.
- A LOCAL FUNCTION USED AT TWO TYPES: `let&` gives it one type (and with
  the types as arguments Rocq prints `Obj.magic`). Write Rocq's own `let`
  of the `fun`: Rocq prints its body at each use; mark it loose.

## 5. Gaps: never hidden

A comment that BEGINS `(* PORT-GAP(kind): words *)`, at the place. The kinds:
`unported` (a function left as a parameter: the mark, `Parameter f : ... ->
M r.` and `Extract Constant f => "fun _ -> Misc.fatal_error
""PORT-GAP(unported): f""".`); `partial` (part of a body replaced by
`fatal_error "PORT-GAP(partial): ..."`); `loose` (ported, but not line
beside line: say what differs; an attribute such as `[@inline]` that is not
kept); `order` (you are not sure of the order of evaluation); `type`,
`verbatim` and `update` (OCaml text of the file, or a setter, that `make
given` cannot check: section 4; such a mark is an error if `make given`
checks EVERY text under it, and the note of lines is enough then); `papp`;
`record-order` (section 2); `init` (a top-level value
that the compiler computes with effects when the module starts: a
`Parameter`, its OCaml text verbatim, and `Extract Inlined Constant x =>
"x".`); `decl`. Prefer a marked
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

A CHANGE THAT ONLY WRITES NAMES OTHERWISE (`tools/samecode.sh REV`; not
part of `make`; CMI_ROOT set as for `make`): it compiles the extracted
files and the runtime of this folder and those of the commit REV and
compares the bytecode instructions that `ocamlc` makes of each
(`-dinstr`). The instructions hold no name of a variable and no spelling
of a module. So a mend that only respells (an abbreviation of a module, a
constructor without its module, a variable without its number) must give
`78 with the same instructions`, and the runtime the same; where the
instructions differ, or a file is on one side only, the script names the
file. From checkpoint 5 to checkpoint 6 all 78 are the same (and the
script says that the runtime has one file more, the empty
`port_abbreviations.ml`). Run it before you send such a mend, and say
the lines that it prints.
WHAT THAT LINE SAYS, AND WHAT IT DOES NOT. It says that `ocamlc`, with
the flags of `tools/check.sh`, makes the same bytecode of the two texts
of each file; both are compiled now, against the same compiled
interfaces and the same `.mli` files of this tree, not against the
compiler as it was at REV. It does NOT say that a constructor written
without its module is the constructor of the same TYPE as before:
constructors of two types can have the same instructions (read the
places, or compare OCaml's typed trees). It says nothing of native code,
and it is not a proof about the program. Two kinds of places are made
blank before the comparison, and nothing else: the place of a failed
assertion (where the instructions build it and raise `Assert_failure` at
once) and the text of a `__LOC__`, both only when they name the file
itself; they change when lines move. The last line of the script counts
them.

THE LINK TEST (`tools/linktest.sh`; not part of `make`): in a SCRATCH work
tree of the compiler, `tools/linktest.sh swap TREE` puts the extracted
files in the place of `middle_end/flambda2/simplify/*.ml`, adds
`runtime/port_monad.ml` and the empty `runtime/port_abbreviations.ml`, and
gives the library `-nolabels -w -a` in its dune file: the one change that
linking needs outside the extracted files and those two.
Build the compiler there before and after the swap (`make boot-compiler`,
`make compiler`) and compare `tools/linktest.sh sums TREE main`: after
the swap the compiler of stage 1 holds the extracted Simplify and compiles
all of stage 2, so an object file that differs is a file that the two
Simplifys do not treat alike. Never commit that tree.
TERMS THAT NO OCAML SOURCE GIVES (`tests/fl/`; not part of `make`): the
compiler's test tool `fexprc` reads a term in Flambda's text form and runs
Simplify on it. `tests/fl/run.sh` runs six such terms through a copy of
`fexprc` built with the compiler's Simplify and one built in the scratch
tree after the swap, and compares the exit status, the output and the
messages. `tests/fl/README.md` says how the copies are built, which
functions each test is for, and what to know to write another.

## 7. What Rocq's text looks like, and known problems to look at later

WHERE THE EXTRACTED TEXT IS NOT THE COMPILER'S (directives alone cannot):
no labels; `let () = e in` for `e;`; a variable that is bound again gets a
number (`dacc0`, `dacc1`), also one with the name of a field of a record
that the file defines; a name that a text of `decl/` holds besides its own
has the whole module name; the cases of a match are in the order of the type;
`a :: []` for `[a]`; an optional argument is the applied text `(fun x__1
x__2 -> F.f ?l:x__1 x__2) None a`; a match on a variant with an inline
record, and the building of such a constructor, are applied functions (`(fun
f__1 f__2 x__0 -> match x__0 with ...) (fun a -> ...) (fun b -> ...) x`);
in EVERY match the body of a case with several patterns, or of `_`, is
written once for each constructor that it stands for (a `_` over a type of
30 constructors is 30 cases); a record that the file defines brings one
function for each field (`let name i = i.name`);
`try`, `match .. with exception`, `while` are calls of `Port_monad`
(`runtime/port_monad.ml`), `lazy e` is `Lazy.from_fun`; a local function is
`let f = fun x -> ...`; each definition has a comment `(** val f : ... **)`
with its Rocq type. The only `open` lines that Rocq writes are `open
Port_monad` and, in some files, `open Port_abbreviations` (an empty module:
see ABBREVIATIONS below): each file of `decl/` ends with an empty module of
its own name, and Rocq then opens no declared unit and prints each declared
name in full (so no name of the file or of OCaml's library can be hidden by
such a line).

ABBREVIATIONS OF MODULES (`tools/aliases.py`, run by `make` for the
extraction of each file; facts found by trying). Rocq keeps the OCaml text
of a declared name under the name by which the file REACHES it, and when an
abbreviation of a module is made (`Module UA := Upwards_acc.`) the texts of
that module are copied for the new names. So `UA.uenv` and
`Upwards_acc.uenv` have each a text, and a directive given later for the
one does not change the other. The tool gives, for the extraction of one
file, the directive `Extract Inlined Constant ...Simplify_import.UA.uenv =>
"UA.uenv".` (and `Extract Inductive` likewise) for each name of each
module that has an abbreviation: the text of `decl/` with the module's
path replaced by the abbreviation. It knows three kinds of abbreviation.
(1) Those of `Simplify_import`, when the file says `Require Import
Simplify_import` and its OCaml head says `open! Simplify_import` (one of
them is left out if the OCaml head binds a module of that name). (2) Those
of the file's own library `abbrev/FILE/Port_abbreviations.v` (section 1).
What Rocq prints by its own name through such a library (a declared type
that takes a parameter, a field of a declared record, a module type), it
prints as the compiler does (`T.Join_analysis.t`), after a line `open
Port_abbreviations` that it writes at the head of the extracted file;
`runtime/port_abbreviations.ml` is that module, and it is empty. (3) Those
that the file makes itself at its left margin, outside any module (`Module
A := P.`): Rocq prints `module A = P` at that place. THIS KIND HAS A COST:
for it Rocq writes down the names of the whole module `P` (its types `t`,
the fields of its records), and then gives a number to each variable of
the file that has one of those names (`t0`, `env_extension0`). Use it
only for a file whose abbreviations are what the file gives to others
(`flow/Flow.v`, `Simplify_import.v`). In all three, the module must be one
that `decl/` declares outside functors and module types.
WHERE ROCQ CHOOSES THE NAME ITSELF (the type of a matched value, which it
takes as `decl/` wrote it: whole), the whole name gets the abbreviation
too, if the file writes that type and its constructors with ONE
abbreviation and never whole, and the abbreviation holds in the whole
extracted file (one of `Simplify_import` that the file does not bind again;
or one that the file makes before its first definition and binds once). So
write a type's constructors in one way in a file. A module that the file
opens (`Import Flambda.Import_.` before the first definition, `open!
Flambda.Import` in the OCaml head) counts as an abbreviation that is empty:
`Named.create_simple` is printed so.
THE FIELDS OF A RECORD of `decl/` have no text: Rocq prints them with the
module name by which the record's TYPE was reached, and through an
abbreviation of `Simplify_import` that is `Simplify_import.S.simples`
(OCaml takes it, but it is not the compiler's text). Where the fields of a
result are read, write the function that gives it whole
(`Simplify_simple.simplify_simples`, as `Simplify_apply_cont_expr.v` does):
the fields are then `Simplify_simple.simples`. A field READ written
through an abbreviation (`sorted.(LCS.innermost_first)`) is printed as a
call, `LCS.innermost_first sorted`, which OCaml refuses: write the field
whole (`sorted.(Lifted_constant_state.innermost_first)`).
CONSTRUCTORS WITHOUT THEIR MODULE. The compiler often writes a constructor
of another module bare (`Unary (Tag_immediate, x)`, `| Naked_float32 ->`),
and OCaml finds the type from the place. A ported file can ask for the
same, TYPE BY TYPE, in a comment before its `Local Open Scope` lines:
`(* CONSTRUCTORS-WITHOUT-MODULE: Flambda_primitive.unary_primitive
Flambda_kind.Boxable_number.t *)` (the names of the inductive types as
`decl/` has them, from the file's name). Every constructor of a listed
type whose OCaml text in `decl/` is a plain path (`M.C`) is then printed
bare in that file, whatever the Rocq text writes (the Rocq text still
needs the module). A constructor whose text is anything else (a function
that builds an inline record, an annotated form) and the text of a
type's eliminator stay as `decl/` has them. List a type when the
compiler's file never writes its constructors with a module, BY ANY
NAME OF THAT MODULE: `Apply.Result_continuation.Never_returns` is a
constructor of `Apply_expr.Result_continuation.t`, because
`Simplify_import.Apply` is `Flambda.Apply`, which is `Apply_expr`. (The
lists of checkpoint 7 were made by a script that looked for such places
through the abbreviations that it knew, and then took off each type with
which a file did not type-check; one place of this kind escaped it and
was found by the review.) If OCaml cannot find the type at some place
(the compiler's file has a type annotation there that the extracted
text has not), the file does not type-check: take the type off the
list. A bare constructor must be the SAME constructor. `tools/samecode.sh`
must say that all 78 files have the same instructions; that shows the
same bytecode, not the same type, so the places are also to be read (at
checkpoint 7 the review compared OCaml's typed trees of the files before
and after: each constructor that lost its module is the same constructor
of the same type).
AFTER THE ABBREVIATIONS, NO `open` AND NO `include` AT THE LEFT MARGIN OF
THE OCAML HEAD (after `open! Simplify_import`, after a line `module A =
P`): such a line could give `A` another meaning than Rocq's, the tool does
not follow it, and `make` stops. Nor may an abbreviation have the name of
a module of `runtime/port_monad.ml` (`Variable_`, `Stdlib_`).
What the tool cannot reach: an abbreviation that is only OCaml text in the
head of the file (Rocq does not know it: the names stay whole; put it in
the file's library); one made inside a module of the file; a name inside a
Rocq functor; a name that a text of `decl/` holds besides its own.

KNOWN PROBLEMS OF THE EXTRACTION (the human has put them off; none is
checked by a tool, but the first in part). In the identity build `M A` is
`A`, and Rocq's extraction takes every term for a pure one:
1. A `let!` that is not used is DROPPED with its call (also one that is the
   second value of a `match a, tmp1 with`, in the cases of `a` that do not
   look at it); used twice it stays a `let`; used under a `fun` or in a
   branch the call MOVES there
   (`let! tmp1 := f x in g (fun y => h tmp1 y)` gives `g (fun y -> h (f x)
   y)`). `make` counts the words only: it does not know scopes or
   shadowing, and it does not look at branches or `fun`s.
2. Rocq's own `let x := f a in k` with `x` used once: the call moves to the
   use; not used: dropped. (Hence `let*`, which is a match and stays.)
   "Once" is once in EACH BRANCH of a match: a `let` whose variable
   stands once in each of two branches is printed in both.
3. A computation that is STORED (in a pair, a record, a variable, a
   top-level definition without arguments) is run when it is built and
   once, not where and as often as the real build says.
4. ETA: `fun x => f a x` may be printed `f a`; if OCaml's `f` acts when it
   has `a` only, the effect moves. The port ASSUMES that it does not; for
   `papp` (section 2) the lint checks it, for these places nothing does.
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
