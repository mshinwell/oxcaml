#!/usr/bin/env python3
#******************************************************************************
#*                                  OxCaml                                    *
#* -------------------------------------------------------------------------- *
#*                               MIT License                                  *
#*                                                                            *
#* Copyright (c) 2026 Jane Street Group LLC                                   *
#* opensource-contacts@janestreet.com                                         *
#*                                                                            *
#* Permission is hereby granted, free of charge, to any person obtaining a    *
#* copy of this software and associated documentation files (the "Software"), *
#* to deal in the Software without restriction, including without limitation  *
#* the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
#* and/or sell copies of the Software, and to permit persons to whom the      *
#* Software is furnished to do so, subject to the following conditions:       *
#*                                                                            *
#* The above copyright notice and this permission notice shall be included    *
#* in all copies or substantial portions of the Software.                     *
#*                                                                            *
#* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
#* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
#* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
#* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
#* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
#* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
#* DEALINGS IN THE SOFTWARE.                                                  *
#******************************************************************************


"""papp.py : the partial applications of declared functions in the ported
files (GUIDE.md, section 2). It follows no file of the compiler.

    pappN F a1 .. aN

gives F its first N arguments only. In OCaml that runs nothing of F when
the FIRST GROUP of parameters of the definition of F has more than N
parameters; the interface does not say so, the definition does.
decl/ARITIES.tsv (made by tools/declgen from the typed trees of the
implementations; decl/README.md, last section, says what a group is) has,
for each declared value, the number of parameters of the function that
decl/ writes as its realisation (0 if the realisation is the name) and the
number of parameters of its definition (- if no definition was read), with
the place. A use PASSES if N is smaller than the first number, or the first
number is 0 and N is smaller than the second. A use that does not pass must
have the mark PORT-GAP(papp); a use that passes must not. (For a function
of the standard library the table has no number: the lint does not judge
such a use, the second step does. THE STANDARD LIBRARY, below.)

Two callers.
- tools/lint.py FILE.v, its fourth check: check(path, raw). With
  LINT_PAPP_ALL in the environment, every use is printed with its verdict.
- papp.py --extracted FILE.v ... (the Makefile's target papp), a second
  step after the lint: see THE EXTRACTED DEFINITIONS below.

THE WRITTEN FORMS. The lint looks for the word pappN (N from 1 to 4)
outside comments and strings. The one form that it reads is

    pappN F        pappN plain, white space, F a name: f or M.f or A.M.f

REFUSED, as an error that names the place, whatever marks there are: pappN
with a module before it (Port_monad.papp1); with @ (@papp1); followed by
anything but such a name (a bracket, @F, a projection, nothing: pappN as a
value). NOT SEEN: a partial application that is reached under another name
(a definition or a notation that stands for pappN, in the kit, in another
library or in the file; in the file the line that makes it is itself
refused, or is read as a use).

THE MARK of a use is a comment that begins (* PORT-GAP(papp): , stands
before the use in the same definition (up to the full stop that ends a
line), and has the function in square brackets as the use writes it:
[Option.map]. A mark names nothing else in square brackets.

A PARTIAL APPLICATION WITHOUT pappN (a definition that is one: [Definition
g : .. := M.f a.]) is seen only through its mark: when a mark names F and
no [pappN F] follows in the definition, the use is the first F after the
mark, and N is the number of arguments that follow it, AS WORDS: a name, a
number, a string, a group in brackets. (For a declared function only: a
mark that names a function of the file wants a [pappN] of it.) If the
application ends with
anything but a closing bracket, a full stop, [;] [,] [|] [:] [=>] or one of
[+ * / < > = ++ :: && ||], N is not known and the mark stays. (A word that
is not an argument of F can only make N too large.) A plain partial
application that has NO MARK IS NOT FOUND.

WHICH FUNCTION. It COUNTS WORDS, as tools/lint.py does. The name F is
looked up among the Rocq names of the table: with its first name replaced,
if that is an abbreviation that FILE.v makes ([Module A := P.], at any
depth) or takes from abbrev/NAME/Port_abbreviations.v (not followed if
these make two of that name with different modules); then as it stands;
then under each module that FILE.v imports ([Require Import] of files of
decl/, [Import P.]), the last first. These sentences are read up to their
full stops, wherever on a line they stand. An abbreviation that decl/
makes is followed. What it does not see: a name that Rocq reads otherwise
because a nearer module has the same name, or because the file imports a
module in another form than these two. (A name without a module that is
found under an import does not pass if a variable of the file may have
the name: A NAME THAT IS ALSO A VARIABLE, below.) A name with a module
that is not found in the table does not pass.

A FUNCTION OF THE FILE: a name without a module that FILE.v binds,
anywhere, by [Definition f], [Fixpoint f], [with f (] or Rocq's own [let
f]; or a name under a module that FILE.v defines. The lint does not judge
it, and leaves a mark that names it alone: its listing says "of the file:
for make papp", and the second step judges the use and its mark (below). A
name without a module that the file does not bind so (a variable: an
argument, a [let!], a pattern) does not pass: what it is bound to is not
known.

THE EXTRACTED DEFINITIONS (--extracted). This is a SECOND STEP after the
lint and no check by itself: it looks only at the uses that the lint
passes or leaves to it (a function of the file, of the standard library),
it does not print the lint's errors again (for a file in which the
lint has one it says so, and that is an error here too), and the Makefile
runs it after the lint has passed for every file. The table reads the
compiler's files. For a function of a file of Simplify that is ported, the
program that is linked runs the definition of extracted/DIR/foo.ml
instead. So, for each use that passes by the number of parameters of a
definition under middle_end/flambda2/simplify/, when extracted/ has that
file:
- THE MODULE of the definition inside its file is read from the table: the
  rows of the file's own unit (the OCaml name begins with Foo.) that have
  the same place say it (Foo.M.f: the module M of foo.ml). There must be
  exactly ONE such module. No such row is an error; so are rows that give
  several modules for the place (Foo.A.f and Foo.B.f: the words do not say
  which of them the use reaches, and a definition that is found in one
  does not stand for the other).
- THE DEFINITION is looked for in that module of the extracted file and
  nowhere else, AS WORDS: a line [let f ..] or [and f ..] (with [rec],
  with attributes) among the items of the module, outside comments and
  strings. The items of a module are the lines that stand at the
  indentation of its first line, between [module M = struct] (also [module
  M : S = struct], and [module M : sig .. end = struct]) and its [end]. A
  functor, or any other line that ends with [struct] or [sig], is a module
  without a name: nothing is found in it. No definition there is an error
  (it fails closed).
- THE PARAMETERS: [let f p1 .. pk = BODY], each of p1 .. pk a plain name,
  [_] or [()], else the count is not known, which is an error. The cases
  of a [function] at the head of BODY are one more. A [fun q1 .. ->] at
  the head of BODY is a second group for OCaml: its parameters are added
  only if every parameter before it is a plain name or [_] (taking those
  in runs nothing), and the count stops at a parameter that is not plain.
  (Rocq's extraction prints its functions with one group.) Each
  definition that is found must have more parameters than the use gives
  arguments.

A FUNCTION OF THE FILE IN THE SECOND STEP. The definition that is linked is
the one of the file's own extracted text, extracted/DIR/foo.ml for
DIR/Foo.v. It is looked for there by the same lookup, in the module where
FILE.v binds the name, and must have more parameters than N AS THE ROCQ USE
WRITES IT. That N is an upper bound of the arguments that the OCaml use
gives ONLY IF Rocq's elaboration adds no argument to what is written. The
extraction adds none and takes some away (the fuel is a proposition, erased
from the definition and from the use). But elaboration, which comes before
it, does add arguments: after a [Section], a function that uses a variable
of the section takes that variable as a first parameter, and every use
inside the section gives it; an implicit parameter that is no type ([{n :
nat}]) is given at every use without being written, and Rocq takes an
implicit parameter from the binders of the head, from the type that the
head declares ([: forall {n : nat}, ..]) and from a [fun] or a [fix] at the
head of the body ([:= fun {n : nat} ..], also after a [let .. in]). Then
the extracted definition has more parameters than the words of the binding
show, the written N is too small, and a use that gives the function all
its parameters would pass. THE TOOL IS NO ELABORATOR. It counts the head of
the binding as it is written, and accepts nothing that Rocq could have
completed: a use of a function of the file is REFUSED unless all of this
holds, as words.
- Neither the binding nor the use stands inside a [Section] (any).
- THE WHOLE HEAD of the binding, from its name to the [:=] of its body, is
  read: binders that are groups in round brackets [(names : type)], plain
  names and [{struct x}]; then, if a colon follows, the type of the result.
  Each type is made of names, round brackets, [->], [*], commas and colons,
  and of nothing else. A brace that is no [{struct x}], a square bracket, a
  backquote, a quote, a number or any other sign anywhere in the head; a
  group that is not [(names : type)]; no [:=] before the full stop (a
  definition by proof): the head is not read, and the use is refused.
- The head WRITES AT LEAST N + 1 PARAMETERS (the names of its groups and
  its plain names). The N arguments of the use, and the parameter after
  them, are then parameters that the head writes in round brackets or as
  plain names: none of them is one that Rocq fills in, whatever the type of
  the result and the body are. A parameter that only the type or the body
  has is not counted.
- The body is no function whose binders the head does not write: after the
  words of the family of [let] that it begins with, each up to its [in],
  its first word is no [fun], [fix] or [cofix]. A body that begins with a
  bracket or another sign, or with a [let] whose [in] is not found, is not
  read. (With N + 1 parameters written this adds nothing that is known to
  matter; it is kept so that a head that the tool counts is the whole list
  of the parameters.)
- EVERY SENTENCE OF THE FILE begins with a word that is known to leave the
  arguments of the function as they are written: [From], [Require],
  [Import], [Module], [Declare Module], [End], [Section], [Variable],
  [Context], [Definition], [Fixpoint], [Inductive], [Record], [Parameter],
  [Extract], [Open Scope] (also after [Local]), and [Arguments] of another
  name. Any other sentence, wherever it stands in the file, refuses the
  use: [Set Implicit Arguments], [Generalizable], [Existing Instance], an
  [Arguments] of the function, a [Notation] or an [Abbreviation] (the name
  of the function, or pappN, may then be another thing), a [Coercion], an
  attribute [#[..]], [Local], [Program], a proof. A sentence is read as
  Rocq reads it, up to a full stop that white space follows, and not line
  by line: a command that follows another on its line is seen.
The bound holds ONLY under these conditions, and there it is stricter than
needed by what is erased: when this was written the 15 such uses were all
[papp1 f fuel], which in OCaml is the bare name f and runs nothing.

For a DECLARED function (and so for a function of another ported file,
which the use reaches by its declared name) the arguments of the OCaml use
are those that are written: a declaration of decl/ is a [Parameter], which
no section changes, and its only implicit parameters are types, which the
extraction erases. The lint checks that of decl/, sentence by sentence:
each sentence begins with [From], [Module], [End], [Parameter],
[Definition], [Inductive], [Record], [Extract] or [Arguments]; a
[Parameter] or a [Definition] has no brace but [{names : Type}], no square
bracket and no backquote; an [Arguments] names a constructor (a name with
a capital). The lint says so if it is not.

A NAME THAT IS ALSO A VARIABLE. The tool does not follow Rocq's scopes: if
the name f of a function of the file also stands, anywhere in the file,
where a variable may be bound, the use is refused, for a nearer variable f
may be what the use reaches. Where a variable may be bound, as words: from
[fun] to its [=>]; from [forall] or [exists] to the comma; from [let] (and
any word that begins with [let] or ends with [!], [*] or [&]: [let!],
[let*], [let&], [let_fuel!], [recursive!]) to its [:=] or [in]; from [fix]
to its [:=]; from [with] or a bar to the next [=>] or [:=] (the patterns of
a [match], the binders of a [with]); the word after [as]; in the head of a
[match] after [in] or [return]; after an opening brace, and after each
[;] that stands directly inside braces (the fields of a record), up to its
[:], bar or [&]; from the first word of a [Definition] or a [Fixpoint] to
its [:=]; and the whole of every other sentence (the constructors of an
[Inductive], a [Parameter], an [Arguments], an [Extract]). The one binding
of f itself is not counted. A use of f elsewhere
(after [=>], after [:=], an argument) is no binder. This reads more as a
binder than Rocq does, never less, as far as the forms above are all the
forms that bind. The lint asks the same of a DECLARED name that the use
writes without a module (one that is found under an import): if it stands
anywhere in the file where a variable may be bound, which is also where
the file would bind it, the use does not pass.

WHERE THE USE STANDS. The name at the use is the binding only where the
binding is in sight and nothing nearer has the name. As words: the use
stands in the sentence of the binding or after it; no sentence between
them begins with [From], [Require] or [Import] (a module that is imported
later may have the name); and the modules that are open at the use begin
with those in which the name as it is written is in sight (for [f], the
modules of the binding; for [X.f], the modules around X). Else the use is
refused.

THE MODULE of a function of the file is that of its binding in FILE.v by
Definition, Fixpoint or [with f (]: the modules that are open there
([Module M.] .. [End M.], as sentences; a [Section] is no module; an [End]
that closes nothing that is open, or a [Module] sentence with both [:=]
and [with], and what is open is not known). For [f] there must be ONE such
binding of f in the whole file. For a name that the use writes with
modules, [X.f], Rocq takes the nearest thing whose name ENDS with X.f,
which need not stand at the root of the file (inside a module Y it may be
Y.X.f). The tool does not follow Rocq's scopes: there must be ONE binding
of f in the whole file whose modules end with X, and that one is taken; if
there are several (X.f at the root and Y.X.f), the use is refused. The use
FAILS, closed, for:
- a local function (bound by Rocq's own [let]) that is not read as A LOCAL
  FUNCTION, below, says;
- a name that the file binds more than once, or both ways; a name with
  modules that several bindings of the file can be, or none;
- a use with modules that stands inside a functor or a module type of the
  file (there the first module may be the functor's parameter);
- a binding inside a functor or a module type of the file, or under a
  module that is no structure in the extracted text (the application of a
  functor);
- a use that stands before the binding, after an import that follows the
  binding, or outside the modules where the name is in sight;
- a section; a head of the binding that is not read whole, or that writes
  no more than N parameters; a body that begins with a function; a
  sentence of the file that is not known (elaboration may add an
  argument); the name standing where a variable may be bound;
- no extracted file, no definition found there, parameters that cannot be
  counted, or no more parameters than N (a definition that is another name
  or an application has 0).
A use that fails and has no mark is an error; one that fails and has the
mark is printed ("keeps its mark"); one that passes and has the mark is an
error (the mark is not needed).

A LOCAL FUNCTION is a name without a module that FILE.v binds by Rocq's
own [let] and in no other way. The second step reads it in ONE shape, and
BY UNIQUENESS, NOT BY SCOPES:
- the file has ONE [let f], and no [Definition f], [Fixpoint f] or [with f
  (]. The binding is written [let f := fix f BINDERS .. := BODY in ..] (a
  local [let rec]: GUIDE.md, section 3). It stands in a sentence that
  begins with [Definition D] or [Fixpoint D], after the first [:=] of that
  sentence that is outside brackets. The name f stands nowhere else in
  the file where a variable may be bound (A NAME THAT IS ALSO A VARIABLE;
  the two names of the binding itself are not counted).
- THE USE stands in the same sentence, where the words say that the
  binding is in sight: in BODY, or in what follows the [in] of the [let].
  As words, that is from the beginning of BODY up to the first of: a
  bracket that closes one that is open there; a bar, [with], [end], [as],
  [return] or comma that is of no [match] that begins after it; an [in]
  that is neither the one of the [let] itself nor of a [let], [let!],
  [let*], [let&], [let_fuel!] or [recursive!] that begins after it; a
  [then] or [else] of no [if] that begins after it; a semicolon that is
  not doubled; the full stop. Only what stands outside the brackets that
  open after the beginning of BODY is read for that. (It may be sooner
  than where Rocq ends the scope; not later, as far as these are all the
  words that end a term.)
- THE CONDITIONS ON ELABORATION are those of a function of the file, with
  the head of the [fix] in the place of the head of the binding: no
  [Section]; every sentence of the file known; the head, from the name
  after [fix] to its [:=], read whole and writing at least N + 1
  parameters; BODY no function.
- IN THE EXTRACTED TEXT there is ONE definition of D among the items of
  the module where FILE.v has the sentence. On the lines of that
  definition (those after its first that are indented more than it) ONE
  line begins [let f] or [and f] (with [rec], with attributes). That
  definition of f has more parameters than N, counted as above.
Anything else fails closed: a local function that is bound by [let f :=
fun ..] or in any other form, or twice, or beside a function of the same
name that the file binds by Definition, Fixpoint or [with]; a use outside
the stretch above; no definition of D, or several; no definition of f
inside it, or several.

THE STANDARD LIBRARY. The table has no number for a value of the standard
library: its row says that the definition is not read (decl/README.md,
the section of ARITIES.tsv). The lint does not judge a use of such a
value: its listing says "of the standard library: for make papp", and it
leaves a mark that names the function alone. The second step reads THE
TREE'S OWN stdlib/, AS WORDS, by the lookup and the count of THE EXTRACTED
DEFINITIONS:
- only for a value of a unit of the library itself: the OCaml name of the
  row is Unit.f; decl/INDEX.tsv says that the value is declared after the
  interface stdlib/unit.mli; and the file is stdlib/unit.ml of the tree.
  A value of a module inside a unit; of the result of a functor (most
  rows: the sets and the maps); under a name that a file of the compiler
  gives a module of the library; an operator: fails closed (the name is
  not Unit.f, or it is declared after another interface, or there is no
  such file).
- stdlib/unit.ml has a line [let f ..] or [and f ..] among the items of
  the file, and EACH such definition has more parameters than N. A value
  that the unit takes from another ([include]) and an [external] have no
  such line, which fails closed. The parameters are plain names, [_] or
  [()]: a label, an optional parameter, a pattern or a type among them is
  not counted, which fails closed.
A use that fails keeps its mark, or wants one; a use that passes has none.
THE LIMIT OF THIS READING. A compiler of the first stage (the one that the
compiler which builds the tree makes of these sources) is linked with the
standard library OF THE COMPILER THAT BUILDS IT. That library is not of
this repository, and NO TOOL HERE READS A DEFINITION OF IT. (Its compiled
interfaces are read, by tools/declgen: the types of what decl/ declares
of the standard library are theirs. decl/README.md, the section of
ARITIES.tsv.) A mark that goes for a function of the standard library
goes on the reading of the tree's own library only: the standard library
of the compiler that this repository makes.

WHAT THE TOOL DOES NOT ESTABLISH. It is NO RESOLVER OF ROCQ'S SCOPES AND NO
ELABORATOR: it reads words. A use that it passes has been checked ONLY
under the shapes that are stated above: pappN in its one written form;
for a function of the file, one binding of the name in the file, the use
after it and in sight of it with no import between, the first N + 1
parameters written in a head that is read whole, no section, no sentence
that is not known, the name nowhere a binder; for a function of another
ported file, one module for the place of its definition; for a local
function and for the standard library, the shapes of their two sections.
Everything else it refuses, or does not see. In particular:
- which binding a name reaches, and which words are binders, is decided by
  the words, not by Rocq's resolution of names. For a declared name that
  is written with a module, nothing checks that a nearer module of the
  same name does not hide it (when the lint's rule was written, Rocq's
  [Locate], asked at the end of each file and not at the place of the use,
  gave the same names for its 121 uses; the tool does not repeat that);
- the term that Rocq elaborates for the function is not looked at, and
  nothing is proved about it. The conditions above are those under which
  the mechanisms that are KNOWN to add an argument (a section, an implicit
  parameter, the commands that make one) cannot have added one among the
  first N + 1 parameters. A COERCION, a canonical structure, a class, or
  any other mechanism of elaboration that the tool does not know is NOT
  implied safe; one that the kit or another library declares is not seen,
  for only the ported file is read;
- a notation of the kit or of another library that gives pappN, or the
  name of the function, another meaning is not seen;
- that pappN of the kit is the plain application of the function to its
  N arguments, which the extraction puts in the place of pappN, is what
  the kit says; the kit is not read here;
- only the one written form of pappN is read. A partial application
  without pappN and without a mark is not found. Where the extraction
  itself changes the shape of a function (it adds or takes away a [fun]),
  only the parameters of the extracted definition are read, as they
  stand; the extracted use is not read;
- for a local function NO SCOPE IS FOLLOWED, of Rocq or of OCaml. In
  their place stand: one binding of the name in the whole file, one
  definition of the name inside the extracted definition, and the place
  of the use as the words give it. A second binding that the words do not
  show (in OCaml, one that does not begin its line) is not seen;
- for a local function THE EXTRACTED USE IS NOT READ. That the extracted
  definition which is found is the one that the use reaches in OCaml
  rests on what the extraction does, which the tool does not check: it
  prints a local function under its name in Rocq, or under another name
  when that one is taken, and then nothing is found;
- the tree's own standard library is read as words, like the extracted
  files, but in a layout that nothing makes uniform (its files are
  written by hand): a definition that is made in another way than by a
  line [let f] or [and f] among the items of its file (by [include], by a
  preprocessor) is not seen, and no typed tree says the count again;
- no definition is read of the standard library of the compiler that
  builds the tree, with which a compiler of the first stage is linked
  (THE LIMIT OF THIS READING, above);
- a definition of any other file whose typed tree was not read keeps its
  mark: nothing is known of it;
- the extracted definition is found as words, in the layout that
  ocamlformat gives the extracted files; what the extraction erases (the
  fuel) makes the rule stricter, not exact;
- a function that is bound by anything but Definition, Fixpoint or [with]
  fails closed."""
import collections
import os
import re
import sys

PNAME = r"[A-Za-z_][A-Za-z_0-9']*"
PPATH = r"%s(?:\.%s)*" % (PNAME, PNAME)
TOOLS = os.path.dirname(os.path.abspath(__file__))
DECL = os.path.join(TOOLS, "..", "decl")
ABBREV = os.path.join(TOOLS, "..", "abbrev")
PORT = os.path.join(TOOLS, "..")
EXTRACTED = os.path.join(TOOLS, "..", "extracted")
SIMPLIFY = "middle_end/flambda2/simplify/"
# the tree's own standard library, and the reason by which a row of the
# table says that a definition is of the standard library, and not read
# (tools/declgen/arities.ml)
STDLIB = os.path.join(TOOLS, "..", "..", "..", "..", "..", "stdlib")
STDLIB_ROW = "not read: the standard library of the tree is compiled by the tree's own compiler"


SPECIAL = re.compile(r'"|\(\*|\*\)')


def blank(s, strings):
    """Rocq text with its comments made blank, in the same length. A string
    is made blank too; or, if [strings], keeps its quotes and has x inside."""
    out = []
    depth = 0
    in_str = False
    i = 0
    for m in SPECIAL.finditer(s + '"'):
        # what stands before this quote or comment sign
        if in_str or depth:
            out.append(re.sub(r"[^\n]", "x" if in_str and strings else " ", s[i:m.start()]))
        else:
            out.append(s[i:m.start()])
        i = m.end()
        t = m.group(0)
        if in_str:
            in_str = t != '"'
            out.append(('"' if strings else " ") if t == '"' else "xx" if strings else "  ")
        elif t == "(*":
            depth += 1
            out.append("  ")
        elif depth:
            depth -= t == "*)"
            out.append(" " * len(t))
        else:
            in_str = t == '"'
            out.append(('"' if strings else " ") if t == '"' else t)
    return "".join(out)[:len(s)]


def read_table():
    """Rocq name -> (parameters of the realisation, parameters of the
    definition or "-", place or reason, OCaml name)."""
    table = {}
    try:
        rows = open(os.path.join(DECL, "ARITIES.tsv")).read().split("\n")
    except IOError:
        rows = []
    for row in rows:
        f = row.split("\t")
        if len(f) == 5:
            table[f[1]] = (int(f[2]), f[3], f[4], f[0])
    return table


# What decl/ would have to say for Rocq to give a declared value an
# argument that is not written: the places, if any.
DECL_IMPLICIT = []
TYPES_ONLY = re.compile(r"\{\s*(?:%s\s+)*%s\s*:\s*Type\s*\}" % (PNAME, PNAME))
DECL_KNOWN = re.compile(
    r"(?:From|Module|End|Parameter|Definition|Inductive|Record|Extract|Arguments)"
    r"(?![A-Za-z_0-9'])"
)


def decl_sentence(text, a, b):
    """Whether the sentence of decl/ from a to b is known to give no
    declared value an argument that is not written: it begins with a word
    of DECL_KNOWN; a [Parameter] or a [Definition] has no brace but
    [{names : Type}], no square bracket and no backquote; an [Arguments]
    names a name with a capital (a constructor)."""
    m = DECL_KNOWN.match(text, a, b)
    if not m:
        return False
    s = text[a:b]
    if m.group(0) in ("Parameter", "Definition"):
        braces = re.findall(r"\{[^}]*\}?", s)
        return all(TYPES_ONLY.fullmatch(x) for x in braces) and "[" not in s and "`" not in s
    if m.group(0) == "Arguments":
        named = ARGUMENTS_OF.match(text, a, b)
        return bool(named) and named.group(1)[0].isupper()
    return True


def decl_abbreviations():
    """[Module A := P.] of decl/, under the whole name of A. Also fills
    DECL_IMPLICIT with the place of each sentence of decl/ that
    [decl_sentence] does not know. The sentences are read whole, up to
    their full stops, with comments and strings blank."""
    out = {}
    for name in sorted(os.listdir(DECL)):
        if not name.endswith(".v"):
            continue
        text = blank(open(os.path.join(DECL, name)).read(), False)
        stack = [name[:-2]]
        for a, b in sentences(text):
            if not decl_sentence(text, a, b):
                DECL_IMPLICIT.append("decl/%s:%d" % (name, text.count("\n", 0, a) + 1))
            m = STRUCTURE.match(text, a, b)
            if not m or m.group(1) == "Section":
                continue
            rest = text[m.end():b]
            if m.group(1) == "End":
                if len(stack) > 1 and stack[-1] == m.group(2):
                    stack.pop()
            elif ":=" not in rest:
                stack.append(m.group(2))
            else:
                target = re.fullmatch(r"\s*:=\s*(%s)\s*" % PPATH, rest)
                if target:
                    out[".".join(stack + [m.group(2)])] = target.group(1)
    return out


def without_library(p):
    for lib in ("SimplifyPort.decl.", "decl."):
        if p.startswith(lib):
            return p[len(lib):]
    return p


def close_of(code, i, end):
    """After the bracket that closes the one at i; None if there is none."""
    depth = 0
    while i < end:
        if code[i] == '"':
            i = code.find('"', i + 1)
            if i < 0:
                return None
        elif code[i] in "([{":
            depth += 1
        elif code[i] in ")]}":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return None


WORD = re.compile(r"@?[A-Za-z_0-9][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
SCOPE = re.compile(r"%[A-Za-z_][A-Za-z_0-9']*")
AFTER = re.compile(r"\.(?:\s|$)|[;,|)\]}:+*/<>=]|&&")
NO_ARGUMENT = ("in", "then", "else", "with", "end", "as", "return")


def count_arguments(code, i, end):
    """The number of arguments that follow a function, from i, as words;
    None if it is not known."""
    n = 0
    while True:
        while i < end and code[i].isspace():
            i += 1
        if i >= end:
            return n
        if code[i] in "([{":
            i = close_of(code, i, end)
        elif code[i] == '"':
            # ["a""b"] is one string
            while i is not None and i < end and code[i] == '"':
                i = code.find('"', i + 1) + 1 or None
        else:
            m = WORD.match(code, i, end)
            if not m or m.group(0) in NO_ARGUMENT:
                break
            i = m.end()
        if i is None:
            return None
        n += 1
        # what follows an argument without a space: [.(field)], [%scope]
        while i < end:
            m = SCOPE.match(code, i, end)
            if code.startswith(".(", i):
                i = close_of(code, i + 1, end)
            elif m:
                i = m.end()
            else:
                break
            if i is None:
                return None
    return n if WORD.match(code, i, end) or AFTER.match(code, i, end) else None


TABLE = None
IN_DECL = None

# A use: where it is, how the listing shows it, whether it is written
# without pappN, the arguments it gives (None: not counted), the function
# as written, the verdict (None for a function of the file; else whether it
# passes, why, the Rocq name in the table; whether it passes is None for a
# function of the standard library, of which the table has no number: the
# second step says), and whether a mark names it.
Use = collections.namedtuple("Use", "pos shown plain n name verdict marked")

PAPP = re.compile(r"(?<![A-Za-z_0-9'])papp([1-4])(?![A-Za-z_0-9'])")
ABBREVIATION = re.compile(r"Module\s+(%s)\s*:=\s*(%s)\s*" % (PNAME, PPATH))
FROM_ABBREV = re.compile(
    r"From\s+SimplifyPort\.abbrev\.(%s)\s+Require\s+Import\s+Port_abbreviations\s*" % PNAME
)
IMPORT_OF_DECL = re.compile(
    r"From\s+SimplifyPort\.decl\s+Require\s+Import\s+([^.]+)|Import\s+(%s)\s*" % PPATH
)
FUNCTION = re.compile(r"\s+(%s)(?![A-Za-z_0-9'.])" % PPATH)


def analyse(path, raw):
    """(the uses, each with its line; the lines to print; the number of
    errors)"""
    global TABLE, IN_DECL
    text = blank(raw, False)
    code = blank(raw, True)
    lines = []
    bad = 0

    def line_of(pos):
        return raw.count("\n", 0, pos) + 1

    # the written forms of pappN: one is read, the others are refused
    papps = []
    for m in PAPP.finditer(text):
        before = text[m.start() - 1] if m.start() else " "
        f = FUNCTION.match(text, m.end())
        refused = (
            "has a module before it"
            if before == "."
            else "is written with @"
            if before == "@"
            else None
            if f
            else "is not followed by the name of a function"
        )
        if refused:
            lines.append(
                "%s:%d: papp%s %s: the lint reads [pappN F] only, pappN plain and F a name"
                % (path, line_of(m.start()), m.group(1), refused)
            )
            bad += 1
        else:
            papps.append((m.start(), int(m.group(1)), f.group(1)))
    marks = [m.start() for m in re.finditer(r"\(\*\s*PORT-GAP\(papp\)", raw)]
    if not papps and not marks:
        return [], lines, bad
    if TABLE is None:
        TABLE = read_table()
        IN_DECL = decl_abbreviations()
    if DECL_IMPLICIT:
        lines.append(
            "%s: decl/ may give a declared value an argument that is not written (an implicit "
            "parameter that is no type, or a command that makes one): %s"
            % (path, " ".join(DECL_IMPLICIT[:5]))
        )
        bad += 1
    # the abbreviations of the file, what it imports and the modules
    # that it defines, sentence by sentence
    own = collections.defaultdict(set)
    imports = []
    defined = set()
    for a, b in sentences(text):
        s = text[a:b]
        m = ABBREVIATION.fullmatch(s)
        if m:
            own[m.group(1)].add(m.group(2))
            continue
        m = FROM_ABBREV.fullmatch(s)
        if m:
            lib = blank(open(os.path.join(ABBREV, m.group(1), "Port_abbreviations.v")).read(), False)
            for c, d in sentences(lib):
                x = ABBREVIATION.fullmatch(lib[c:d])
                if x:
                    own[x.group(1)].add(x.group(2))
            continue
        m = IMPORT_OF_DECL.fullmatch(s)
        if m:
            imports.extend(m.group(1).split() if m.group(1) else [m.group(2)])
            continue
        m = STRUCTURE.match(s)
        if m and m.group(1).startswith("Module"):
            defined.add(m.group(2))
    defined -= set(own)
    # the functions that the file binds
    bound = set(
        re.findall(
            r"(?<![A-Za-z_0-9'.])(?:Definition|Fixpoint|let)\s+(%s)(?![A-Za-z_0-9'.])" % PNAME,
            text,
        )
    ) | set(re.findall(r"(?<![A-Za-z_0-9'.])with\s+(%s)\s*[({]" % PNAME, text))

    def chase(name):
        for _ in range(30):
            name = without_library(name)
            if name in TABLE:
                return name
            parts = name.split(".")
            for k in range(len(parts) - 1, 0, -1):
                target = IN_DECL.get(".".join(parts[:k]))
                if target:
                    name = ".".join([target] + parts[k:])
                    break
            else:
                return None
        return None

    def resolve(f):
        """The Rocq name of f in the table; None if it is not there."""
        name = f
        for _ in range(10):
            head, _, rest = name.partition(".")
            if not rest or head not in own:
                break
            if len(own[head]) != 1:
                return None
            name = list(own[head])[0] + "." + rest
        for t in [name] + [p + "." + name for p in reversed(imports)]:
            found = chase(t)
            if found:
                return found
        return None

    def verdict(n, f):
        """(passes, why, Rocq name); None for a function of the file."""
        found = resolve(f)
        if found is None:
            if "." not in f:
                if f in bound:
                    return None
                why = (
                    "%s has no module, and the file does not bind it by Definition, Fixpoint, "
                    "with or let: what it is bound to is not known" % f
                )
                return False, why, None
            if f.split(".")[0] in defined:
                return None
            return False, "%s is not among the declared values of decl/ARITIES.tsv" % f, None
        if "." not in f:
            # a declared name that is found under an import: a nearer
            # binding of the file may be what the use reaches
            places = may_be_bound(text, f, -1)
            if places:
                why = (
                    "%s is a declared value under an import, and also stands where the file "
                    "may bind it (line %s): the words do not say which the use reaches"
                    % (f, ", ".join(str(k) for k in places[:5]))
                )
                return False, why, found
        wrapper, definition, where, _ = TABLE[found]
        if wrapper:
            why = "the realisation of %s in decl/ is a function of %d parameters" % (found, wrapper)
            return n < wrapper, why, found
        if definition == "-":
            # (None: the standard library, which the second step reads)
            return None if where == STDLIB_ROW else False, "%s: %s" % (found, where), found
        why = "the definition of %s has %s parameter%s (%s)" % (
            found,
            definition,
            "" if definition == "1" else "s",
            where,
        )
        return n < int(definition), why, found

    uses = [
        Use(pos, "papp%d %s" % (n, f), False, n, f, verdict(n, f), False) for pos, n, f in papps
    ]
    # each mark: the names in its square brackets, and where its definition ends
    covered = set()
    stop_re = re.compile(r"\.\s*\n")
    for start in marks:
        depth = 0
        i = start
        while i < len(raw):
            if raw.startswith("(*", i):
                depth += 1
                i += 2
            elif raw.startswith("*)", i):
                depth -= 1
                i += 2
                if depth == 0:
                    break
            else:
                i += 1
        names = re.findall(r"\[(%s)\]" % PPATH, raw[start:i])
        stop = stop_re.search(text, i)
        end = stop.start() if stop else len(text)
        where = "%s:%d: the mark PORT-GAP(papp)" % (path, line_of(start))
        if not names:
            lines.append("%s names no function in square brackets" % where)
            bad += 1
        for name in names:
            same = resolve(name)
            mine = [
                u
                for u in uses
                if not u.plain
                and i <= u.pos < end
                and (u.name == name or (same is not None and same == resolve(u.name)))
            ]
            if not mine:
                # a partial application that is not written with pappN
                m = re.compile(
                    r"(?<![A-Za-z_0-9'.@])%s(?![A-Za-z_0-9'.])" % re.escape(name)
                ).search(code, i, end)
                if not m:
                    lines.append(
                        "%s names %s, which does not follow in the definition" % (where, name)
                    )
                    bad += 1
                    continue
                n = count_arguments(code, m.end(), end)
                if n is None:
                    v = (False, "its arguments could not be counted", None)
                    shown = "%s, arguments not counted" % name
                else:
                    v = verdict(n, name)
                    shown = "%s, %d argument%s counted as words" % (name, n, "" if n == 1 else "s")
                if v is None:
                    # (the first F after the mark may be its own binding)
                    lines.append(
                        "%s names %s, a function of the file, of which no pappN follows in the definition"
                        % (where, name)
                    )
                    bad += 1
                    continue
                mine = [Use(m.start(), shown, True, n, name, v, False)]
                uses.append(mine[0])
            # a mark stays for a use that does not pass, and for a function
            # of the file or of the standard library (the second step judges
            # those)
            staying = [u for u in mine if u.verdict is None or not u.verdict[0]]
            for u in staying:
                covered.add(u.pos)
            if staying:
                continue
            bad += 1
            lines.append(
                "%s names %s, which needs none: %s: %s"
                % (where, name, mine[0].shown, mine[0].verdict[1])
            )
    uses = [u._replace(marked=u.pos in covered) for u in sorted(uses, key=lambda u: u.pos)]
    for u in uses:
        if os.environ.get("LINT_PAPP_ALL"):
            word = (
                "of the file: for make papp"
                if u.verdict is None
                else "not counted"
                if u.n is None
                else "of the standard library: for make papp"
                if u.verdict[0] is None
                else ("passes" if u.verdict[0] else "does not pass")
                + (" (arguments counted as words)" if u.plain else "")
            )
            why = "" if u.verdict is None else u.verdict[1]
            print("%s:%d\t%s\t%s\t%s" % (path, line_of(u.pos), u.shown, word, why))
        if u.verdict is None or u.verdict[0] is not False:
            continue
        here = "%s:%d: %s" % (path, line_of(u.pos), u.shown)
        if u.pos in covered:
            lines.append("%s keeps its mark PORT-GAP(papp): %s" % (here, u.verdict[1]))
        else:
            lines.append(
                "%s has no mark PORT-GAP(papp) with [%s] before it, and is not known to run nothing: %s"
                % (here, u.name, u.verdict[1])
            )
            bad += 1
    return [(line_of(u.pos), u) for u in uses], lines, bad


def check(path, raw):
    """For tools/lint.py: the lines to print and the number of errors."""
    _, lines, bad = analyse(path, raw)
    return lines, bad


PLAIN = re.compile(r"[a-z_][A-Za-z0-9_']*")
FUNCTION_CASES = re.compile(r"function(?![A-Za-z0-9_'])")


def count_parameters(rest):
    """The parameters of [p1 .. pk = BODY] that are taken before anything
    runs; None if one of p1 .. pk is not a plain name, [_] or [()]. The
    cases of a [function] at the head of BODY are one more. A [fun q1 ..
    ->] at the head of BODY is a second group: it is counted only if every
    parameter so far is a plain name or [_], and as far as its parameters
    are plain."""
    head, eq, body = rest.partition("=")
    if not eq:
        return None
    group = head.split()
    if not all(PLAIN.fullmatch(w) or w == "()" for w in group):
        return None
    n = len(group)
    body = body.strip()
    while True:
        if FUNCTION_CASES.match(body):
            return n + 1
        m = re.match(r"fun\s+([^-]*?)->", body)
        if not m or not all(PLAIN.fullmatch(w) for w in group):
            return n
        group = m.group(1).split()
        for w in group:
            if not (PLAIN.fullmatch(w) or w == "()"):
                return n
            n += 1
        body = body[m.end():].strip()


def blank_ocaml(s):
    """OCaml text with its comments made blank and x inside its strings,
    line for line."""
    out = []
    depth = 0
    i = 0
    in_str = False
    while i < len(s):
        c = s[i]
        if in_str:
            if c == "\\" and i + 1 < len(s):
                out.append("xx" if depth == 0 else "  ")
                i += 2
                continue
            if c == '"':
                in_str = False
                out.append(c if depth == 0 else " ")
            else:
                out.append("\n" if c == "\n" else "x" if depth == 0 else " ")
            i += 1
        elif s.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and s.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif c == '"' and not (i > 0 and s[i - 1] == "'" and s[i + 1:i + 2] == "'"):
            # a string (OCaml reads one inside a comment too); not the
            # character ['"']
            in_str = True
            out.append(c if depth == 0 else " ")
            i += 1
        else:
            out.append(c if depth == 0 or c == "\n" else " ")
            i += 1
    return "".join(out)


UNAME = r"[A-Z][A-Za-z0-9_']*"
OPENS = re.compile(r"(?<![A-Za-z0-9_'])(struct|sig)$")
MODULE_STRUCT = re.compile(r"module\s+(%s)\s*(?::[^=()]*)?=\s*struct$" % UNAME)
MODULE_SIG = re.compile(r"module\s+(%s)\s*:\s*sig$" % UNAME)


def definition_of(name):
    """A line on which a definition of [name] begins: what follows the
    name on it."""
    return re.compile(
        r"(?:let|and)(?:\s*\[@[^\]]*\])*(?:\s+rec(?![A-Za-z0-9_']))?(?:\s*\[@[^\]]*\])*"
        r"\s+%s(?![A-Za-z0-9_'])(.*)$" % re.escape(name)
    )


def parameters_at(lines, k, rest):
    """The parameters of the definition that begins on the line k, [rest]
    being what follows its name there."""
    return count_parameters(" ".join([rest] + lines[k + 1:k + 8]))


def definition_lines(text, modules, name):
    """The lines of an OCaml text, its comments blank; and the definitions
    of [name] among the items of the module [modules] (a list of names;
    empty for the file itself): (the number of the line, what follows the
    name on it)."""
    definition = definition_of(name)
    out = []
    lines = blank_ocaml(text).split("\n")
    # the structures and signatures that are open: [name or None, the
    # indentation of the line that opens it, that of its items or None,
    # whether it is a signature]
    stack = []
    for k, line in enumerate(lines):
        s = line.strip()
        if not s:
            continue
        indent = len(line) - len(line.lstrip())
        if stack and stack[-1][2] is None and indent > stack[-1][1]:
            stack[-1][2] = indent
        if stack and indent == stack[-1][1] and re.match(r"end(?![A-Za-z0-9_'])", s):
            if stack[-1][3] and re.fullmatch(r"end\s*=\s*struct", s):
                stack[-1][2:] = [None, False]
            else:
                stack.pop()
            continue
        at_item = indent == (stack[-1][2] if stack else 0)
        opens = OPENS.search(s)
        if opens:
            m = (MODULE_STRUCT.fullmatch(s) or MODULE_SIG.fullmatch(s)) if at_item else None
            stack.append([m.group(1) if m else None, indent, None, opens.group(1) == "sig"])
            continue
        if not at_item or any(f[3] for f in stack) or [f[0] for f in stack] != list(modules):
            continue
        m = definition.match(s)
        if m:
            out.append((k, m.group(1)))
    return lines, out


def extracted_definitions(text, modules, name):
    """The numbers of parameters (None: not known) of the definitions of
    [name] among the items of the module [modules] (a list of names; empty
    for the file itself) of an extracted file."""
    lines, found = definition_lines(text, modules, name)
    return [parameters_at(lines, k, rest) for k, rest in found]


def extracted_local(text, modules, outer, name):
    """The numbers of parameters (None: not known) of the definitions of
    [name] that stand inside the ONE definition of [outer] among the items
    of the module [modules] of an extracted file: on the lines after its
    first that are indented more than it, each line that begins [let name]
    or [and name]. None if [outer] has not exactly one definition there."""
    lines, found = definition_lines(text, modules, outer)
    if len(found) != 1:
        return None
    k = found[0][0]
    margin = len(lines[k]) - len(lines[k].lstrip())
    definition = definition_of(name)
    out = []
    for j in range(k + 1, len(lines)):
        s = lines[j].strip()
        if not s:
            continue
        if len(lines[j]) - len(lines[j].lstrip()) <= margin:
            break
        m = definition.match(s)
        if m:
            out.append(parameters_at(lines, j, m.group(1)))
    return out


END = re.compile(r"\.(?=\s|$)")


def sentences(text):
    """The sentences of a Rocq text whose comments and strings are blank,
    in order: (where the first word is, where the full stop is). A sentence
    ends at a full stop that white space or the end of the text follows,
    wherever on a line it stands."""
    out = []
    i = 0
    for m in END.finditer(text):
        while i < m.start() and text[i].isspace():
            i += 1
        out.append((i, m.start()))
        i = m.end()
    return out


def sentence_at(spans, pos):
    """The number of the sentence that pos stands in (the number of
    sentences, if no full stop follows pos)."""
    lo, hi = 0, len(spans)
    while lo < hi:
        mid = (lo + hi) // 2
        if spans[mid][1] < pos:
            lo = mid + 1
        else:
            hi = mid
    return lo


STRUCTURE = re.compile(
    r"(Module\s+Type|Module|Section|End)\s+(?:(?:Import|Export)\s+)?(%s)(?![A-Za-z_0-9'])" % PNAME
)
WITH = re.compile(r"(?<![A-Za-z_0-9'.])with(?![A-Za-z_0-9'])")


def open_at(text, spans, pos):
    """What is open at pos, from the outermost, as words: (name, kind), the
    kind "module", "section", or None for a functor, a module type or a
    module of which the words do not say whether it is open. None if the
    words do not say what is open: an [End] that closes nothing."""
    stack = []
    for a, b in spans:
        if a >= pos:
            break
        m = STRUCTURE.match(text, a, b)
        if not m:
            continue
        kind = " ".join(m.group(1).split())
        name = m.group(2)
        rest = text[m.end():b]
        if kind == "End":
            if not stack or stack[-1][0] != name:
                return None
            stack.pop()
        elif kind == "Section":
            stack.append((name, "section"))
        elif ":=" in rest and not WITH.search(rest):
            pass  # [Module A := P.] is one sentence
        elif kind == "Module Type" or "(" in rest or ":=" in rest:
            stack.append((name, None))
        else:
            stack.append((name, "module"))
    return stack


def rocq_modules(text, spans, pos):
    """The modules of FILE.v that are open at pos, from the outermost, as
    words; None if one of them is a functor or a module type, or if the
    words do not say what is open."""
    stack = open_at(text, spans, pos)
    if stack is None or any(kind is None for _, kind in stack):
        return None
    return [name for name, kind in stack if kind == "module"]


def in_section(text, spans, pos):
    """Whether a [Section] is open at pos, as words (true also if the words
    do not say what is open)."""
    stack = open_at(text, spans, pos)
    return stack is None or any(kind == "section" for _, kind in stack)


HEAD_TOKEN = re.compile(r":=|->|(?P<word>%s)|\S" % PPATH)
GROUP = re.compile(r"\(\s*((?:%s\s+)*%s)\s*:(?!=)(.*)\)" % (PNAME, PNAME), re.S)
STRUCT = re.compile(r"\{\s*struct\s+%s\s*\}" % PNAME)
BODY = re.compile(":=")


def plain_type(text, i, end):
    """Whether the text from i to end is a type of which the tool reads
    every word: names, round brackets that close, [->], [*], commas and
    colons, and nothing else (no brace, no square bracket, no backquote)."""
    depth = 0
    while True:
        m = HEAD_TOKEN.search(text, i, end)
        if not m:
            return depth == 0
        t = m.group(0)
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
            if depth < 0:
                return False
        elif not (m.group("word") or t in ("->", "*", ",", ":")):
            return False
        i = m.end()


def written_head(text, pos, end):
    """The head of a binding, from the end of its name at pos to the [:=]
    of its body, in the sentence whose full stop is at [end]: (the number
    of parameters that it writes, where the body begins); or (None, why)
    if it is not read whole. What is read: binders that are groups [(names
    : type)], plain names and [{struct x}]; then, after a colon, the type
    of the result; each type as [plain_type] reads it."""
    n = 0
    i = pos
    while True:
        m = HEAD_TOKEN.search(text, i, end)
        if not m:
            return None, "no [:=] before the full stop"
        t = m.group(0)
        i = m.end()
        if t == ":=":
            return n, i
        if t == ":":
            break
        if t == "(":
            j = close_of(text, m.start(), end)
            g = GROUP.fullmatch(text, m.start(), j) if j else None
            if not g or not plain_type(text, g.start(2), g.end(2)):
                return None, "a binder in brackets that is not [(names : type)] with a type that is read"
            n += len(g.group(1).split())
            i = j
        elif t == "{":
            j = close_of(text, m.start(), end)
            if not j or not STRUCT.fullmatch(text, m.start(), j):
                return None, "a binder in braces"
            i = j
        elif m.group("word") and "." not in t:
            n += 1
        else:
            return None, "[%s] among the binders" % t
    m = BODY.search(text, i, end)
    if not m:
        return None, "no [:=] before the full stop"
    if not plain_type(text, i, m.start()):
        return None, "a type of the result that is not read"
    return n, m.end()


TOKEN = re.compile(
    r"\{\||\|\}|\|\||:=|=>|(?P<word>%s[!*&]?)|(?P<end>\.(?=\s|$))|[(){}\[\]]|\S" % PPATH
)


def of_let(t):
    """Whether the word t is [let] or of its family in the kit: it begins
    with [let] or ends with [!], [*] or [&] ([let!], [let*], [let&],
    [let_fuel!], [recursive!])."""
    return t.startswith("let") or t[-1] in "!*&"


def after_in(text, i, end):
    """After the [in] of a word of the family of [let] whose text begins at
    i; None if it is not found before [end]. Outside brackets, each word
    of the family wants one [in]; the [in]s between a [match] and its
    [with] are not counted; a [return] elsewhere is not read."""
    depth = 0
    wanted = 1
    heads = 0
    for m in TOKEN.finditer(text, i, end):
        t = m.group(0)
        if t in ("(", "[", "{"):
            depth += 1
        elif t in (")", "]", "}"):
            depth -= 1
            if depth < 0:
                return None
        elif depth or not m.group("word"):
            continue
        elif t == "match":
            heads += 1
        elif t == "with":
            heads = max(0, heads - 1)
        elif t == "in":
            if not heads:
                wanted -= 1
                if wanted == 0:
                    return m.end()
        elif t == "return":
            if not heads:
                return None
        elif of_let(t):
            wanted += 1
    return None


def function_at_the_head(text, i, end):
    """Why the body from i to [end] may be a function whose binders the
    head of the binding does not write; None if it is none: after the
    words of the family of [let] that it begins with, each up to its [in],
    its first word is a name or a word that is no [fun], [fix] or [cofix].
    A body that begins with a bracket or another sign is not read; nor is
    Rocq's own [let] when a pattern follows it, not a name (it may have a
    second [in], after [return])."""
    for _ in range(1000):
        m = TOKEN.search(text, i, end)
        if not m:
            return "it has no word"
        t = m.group(0)
        if not m.group("word"):
            return "it begins with [%s], which the tool does not read" % t
        if t in ("fun", "fix", "cofix"):
            return "it begins with [%s], whose binders the head does not write" % t
        if not of_let(t):
            return None
        bound = TOKEN.search(text, m.end(), end)
        if t == "let" and not (bound and bound.group("word")):
            return "its [let] binds a pattern, which the tool does not follow"
        i = after_in(text, m.end(), end)
        if i is None:
            return "the [in] of its [%s] is not found" % t
    return "it is too long"


FAMILY = ("let", "let!", "let*", "let&", "let_fuel!", "recursive!")


def after_first_define(text, a, end):
    """After the first [:=] of the text from a to [end] that stands outside
    brackets; None if there is none."""
    depth = 0
    for m in TOKEN.finditer(text, a, end):
        t = m.group(0)
        if t in ("(", "[", "{", "{|"):
            depth += 1
        elif t in (")", "]", "}", "|}"):
            depth -= 1
        elif t == ":=" and depth == 0:
            return m.end()
    return None


def end_of_scope(text, i, end):
    """Where the name of a local function [let f := fix f .. := BODY in ..]
    is no longer known to be in sight, as words, from the beginning i of
    BODY: [end]; or before it the first bracket that closes one that is
    open at i; the first bar, [with], [end], [as], [return] or comma that
    is of no [match] that begins after i; the first [in] that is neither
    the one of the [let] itself (the first that is of no word of FAMILY
    after i) nor of a word of FAMILY after i; the first [then] or [else] of
    no [if] that begins after i; the first semicolon that is not doubled.
    Only what stands outside the brackets that open after i is read. This
    may be sooner than where Rocq ends the scope; not later, as far as
    these are all the words that end a term."""
    depth = 0
    matches = 0
    thens = 0
    elses = 0
    lets = 1  # the [in] of the [let] itself is still to come
    for m in TOKEN.finditer(text, i, end):
        t = m.group(0)
        if t in ("(", "[", "{", "{|"):
            depth += 1
        elif t in (")", "]", "}", "|}"):
            depth -= 1
            if depth < 0:
                return m.start()
        elif depth:
            continue
        elif t == "match":
            matches += 1
        elif t == "end":
            if not matches:
                return m.start()
            matches -= 1
        elif t in ("|", "with", "as", "return", ","):
            if not matches:
                return m.start()
        elif t in FAMILY:
            lets += 1
        elif t == "in":
            if not lets:
                return m.start()
            lets -= 1
        elif t == "if":
            thens += 1
        elif t == "then":
            if not thens:
                return m.start()
            thens -= 1
            elses += 1
        elif t == "else":
            if not elses:
                return m.start()
            elses -= 1
        elif t == ";":
            if text[m.start() - 1] != ";" and text[m.end():m.end() + 1] != ";":
                return m.start()
    return end


KNOWN = re.compile(
    r"(?:From|Require|Import|Module|Declare\s+Module|End|Section|Variable|Context|Definition"
    r"|Fixpoint|Inductive|Record|Parameter|Extract|(?:Local\s+)?Open\s+Scope|Arguments)"
    r"(?![A-Za-z_0-9'])"
)
IMPORTS = re.compile(r"(?:From|Require|Import)(?![A-Za-z_0-9'])")
ARGUMENTS_OF = re.compile(r"Arguments\s+(?:%s\.)*(%s)(?![A-Za-z_0-9'.])" % (PNAME, PNAME))


def not_known(text, spans, f):
    """The first sentence of the file that the tool does not know to leave
    the arguments of f as they are written: (its line, its first words);
    None if there is none. Known: a sentence that begins with one of the
    words of KNOWN, but an [Arguments] only if it names another name than
    f. (So not known: [Set ..], [Generalizable], [Existing Instance],
    [Notation], [Abbreviation], [Coercion], [Local ..] but [Local Open
    Scope], an attribute [#[..]], a proof, and every other.)"""
    for a, b in spans:
        m = KNOWN.match(text, a, b)
        if m and m.group(0) == "Arguments":
            m = ARGUMENTS_OF.match(text, a, b)
            if m and m.group(1) == f:
                m = None
        if not m:
            return text.count("\n", 0, a) + 1, " ".join(text[a:b].split()[:3])
    return None


def may_be_bound(text, f, binding, also=()):
    """The places (lines) where the word f stands and a variable may be
    bound, as words; the name of the binding at [binding] is not counted,
    nor one at a place of [also] (the [fix f] of a local [let f])."""
    out = []
    depth = 0
    kinds = []  # the brackets that are open
    regions = []  # (the tokens that end it, the depth where it began)
    heads = []  # the depths of the [match]es whose [with] has not come
    start = True  # at the first word of a sentence
    after_as = False
    for m in TOKEN.finditer(text):
        t = m.group(0)
        if start:
            # a sentence: up to its [:=] if it is a Definition or a
            # Fixpoint (a body follows), else to its end
            regions.append(((":=",) if t in ("Definition", "Fixpoint") else (), depth))
            start = False
        if t in ("(", "[", "{"):
            depth += 1
            kinds.append(t)
            if t == "{":
                regions.append(((":", "|", "&"), depth))
        elif t in (")", "]", "}"):
            depth -= 1
            kinds = kinds[:-1]
            regions = [r for r in regions if r[1] <= depth]
            heads = [d for d in heads if d <= depth]
        elif m.group("end") and depth == 0:
            regions = []
            heads = []
            start = True
            continue
        else:
            regions = [r for r in regions if not (t in r[0] and r[1] == depth)]
        word = m.group("word")
        if (
            word
            and t == f
            and (regions or after_as)
            and m.start() != binding
            and m.start() not in also
        ):
            line = text.count("\n", 0, m.start()) + 1
            if line not in out:
                out.append(line)
        after_as = False
        if t == ";" and kinds and kinds[-1] == "{":
            # the next field of a record
            regions.append(((":", "|", "&"), depth))
        if not word and t != "|":
            continue
        if t == "fun":
            regions.append((("=>",), depth))
        elif t in ("forall", "exists", "exists2"):
            regions.append(((",",), depth))
        elif of_let(t):
            regions.append(((":=", "in"), depth))
        elif t in ("fix", "cofix"):
            regions.append(((":=",), depth))
        elif t == "match":
            heads.append(depth)
        elif t == "with":
            if heads and heads[-1] == depth:
                heads.pop()
            regions.append((("=>", ":="), depth))
        elif t == "|":
            regions.append((("=>", ":="), depth))
        elif t == "as":
            after_as = True
        elif t in ("in", "return") and heads and heads[-1] == depth:
            regions.append((("with",), depth))
    return out


def extracted_of(path):
    """The extracted file of FILE.v: (how it is shown, its text or None)."""
    rel = os.path.relpath(os.path.abspath(path), os.path.abspath(PORT))
    rel = os.path.join(os.path.dirname(rel), os.path.basename(rel)[:-2].lower() + ".ml")
    try:
        return "extracted/" + rel, open(os.path.join(EXTRACTED, rel)).read()
    except IOError:
        return "extracted/" + rel, None


LOCAL = r"let\s+(%s)\s*:=\s*fix\s+(%s)(?![A-Za-z_0-9'.])"
OUTER = re.compile(r"(?:Definition|Fixpoint)\s+(%s)(?![A-Za-z_0-9'.])" % PNAME)


def of_a_local(path, text, spans, u, f, at):
    """(whether it passes, why) for a use of a local function of the file,
    whose one [let f] stands at [at]: A LOCAL FUNCTION, above."""
    m = re.compile(LOCAL % (re.escape(f), re.escape(f))).match(text, at)
    if not m:
        return False, (
            "%s is a local function that is not written [let %s := fix %s ..]: "
            "the tool reads no other" % (f, f, f)
        )
    first = sentence_at(spans, at)
    if first == len(spans):
        return False, "no full stop ends the binding of %s" % f
    a, end = spans[first]
    outer = OUTER.match(text, a, end)
    body = after_first_define(text, a, end)
    if not outer or body is None or at < body:
        return False, (
            "the local function %s does not stand in the body of a Definition or a Fixpoint" % f
        )
    modules = rocq_modules(text, spans, a)
    if modules is None:
        return False, "%s is bound inside a functor or a module type of the file" % f
    places = may_be_bound(text, f, m.start(1), (m.start(2),))
    if places:
        return False, (
            "%s also stands where a variable may be bound (line %s): "
            "the words do not say which the use reaches"
            % (f, ", ".join(str(n) for n in places[:5]))
        )
    # as for a function of the margin, with the head of the [fix]
    head = written_head(text, m.end(2), end)
    other = not_known(text, spans, f)
    added = (
        "a [Section]"
        if in_section(text, spans, a)
        else "line %d begins with [%s], a sentence that the tool does not know to add none" % other
        if other
        else "the head of the [fix] of %s, from its name to [:=], is not read: %s" % (f, head[1])
        if head[0] is None
        else "the head of the [fix] of %s writes %d parameter%s and the use gives %d argument%s: "
        "a parameter that the head does not write is not counted"
        % (f, head[0], "" if head[0] == 1 else "s", u.n, "" if u.n == 1 else "s")
        if head[0] <= u.n
        else None
    )
    if not added:
        added = function_at_the_head(text, head[1], end)
        if added:
            added = "the body of %s: %s" % (f, added)
    if added:
        return False, "Rocq may give %s an argument that is not written (%s)" % (f, added)
    # the use stands where the words say that the binding is in sight
    limit = end_of_scope(text, head[1], end)
    if not head[1] <= u.pos < limit:
        return False, (
            "the use does not stand where the words say that the local function %s is in sight "
            "(the body of its [fix], and what follows the [in] of its [let], up to line %d): "
            "the words do not say what %s is there" % (f, text.count("\n", 0, limit) + 1, f)
        )
    shown, ml = extracted_of(path)
    if ml is None:
        return False, "%s is not there" % shown
    d = outer.group(1)
    found = extracted_local(ml, modules, d, f)
    inside = ".".join(modules) if modules else "the file"
    if found is None:
        return False, "%s has not one definition among the items of %s in %s" % (d, inside, shown)
    if len(found) != 1:
        return False, "%d lines begin a definition of %s inside the definition of %s in %s" % (
            len(found),
            f,
            d,
            shown,
        )
    if found[0] is None:
        return False, "the parameters of the local function %s in %s could not be counted" % (
            f,
            shown,
        )
    why = "the local function %s has %d parameter%s inside %s in %s, and is given %d argument%s" % (
        f,
        found[0],
        "" if found[0] == 1 else "s",
        d,
        shown,
        u.n,
        "" if u.n == 1 else "s",
    )
    return found[0] > u.n, why


INTERFACES = None


def interface_of(rocq):
    """The interface after which decl/ declares the value of that Rocq
    name: the last column of its row of decl/INDEX.tsv; None if it has no
    row there."""
    global INTERFACES
    if INTERFACES is None:
        INTERFACES = {}
        try:
            rows = open(os.path.join(DECL, "INDEX.tsv")).read().split("\n")
        except IOError:
            rows = []
        for row in rows:
            f = row.split("\t")
            if len(f) == 5 and f[2] == "value":
                INTERFACES[f[1]] = f[4]
    return INTERFACES.get(rocq)


def of_the_stdlib(u):
    """(whether it passes, why) for a use of a function of the standard
    library, of which the table has no number: by the tree's own stdlib/,
    read as words. THE STANDARD LIBRARY, above."""
    ocaml = TABLE[u.verdict[2]][3]
    parts = ocaml.split(".")
    if len(parts) != 2 or not re.fullmatch(UNAME, parts[0]) or not PLAIN.fullmatch(parts[1]):
        return False, (
            "%s is not written Unit.f, a value of a unit of the standard library itself (it is "
            "of a module inside a unit, or of the result of a functor, or an operator): "
            "the tool does not look for it in stdlib/" % ocaml
        )
    unit, name = parts
    source = unit[0].lower() + unit[1:] + ".ml"
    shown = "stdlib/" + source
    declared = interface_of(u.verdict[2])
    if declared != shown + "i":
        return False, (
            "decl/INDEX.tsv does not say that %s is declared after %si (it says %s): "
            "the tool does not take %s for a unit of the standard library"
            % (ocaml, shown, declared or "nothing", unit)
        )
    try:
        text = open(os.path.join(STDLIB, source)).read()
    except IOError:
        return False, "%s is not there" % shown
    found = extracted_definitions(text, [], name)
    if not found:
        return False, "no definition of %s is found among the items of %s" % (name, shown)
    if None in found:
        return False, "the parameters of %s in %s could not be counted" % (name, shown)
    k = min(found)
    why = "%s has %d parameter%s in %s of the tree, and is given %d argument%s" % (
        name,
        k,
        "" if k == 1 else "s",
        shown,
        u.n,
        "" if u.n == 1 else "s",
    )
    return k > u.n, why


def of_the_file(path, text, u):
    """(whether it passes, why) for a use of a function of the file, by
    the file's own extracted text."""
    if u.n is None:
        return False, "its arguments could not be counted"
    spans = sentences(text)
    parts = u.name.split(".")
    f = parts[-1]
    written = parts[:-1]
    ahead = r"(?<![A-Za-z_0-9'.])"
    behind = r"(?![A-Za-z_0-9'.])"
    # where the file binds f by Definition, Fixpoint or with: the places
    # of the name
    margin = [
        m.start(1) if m.group(1) else m.start(2)
        for m in re.finditer(
            r"%s(?:(?:Definition|Fixpoint)\s+(%s)%s|with\s+(%s)\s*[({])"
            % (ahead, re.escape(f), behind, re.escape(f)),
            text,
        )
    ]
    here = rocq_modules(text, spans, u.pos)
    if written:
        # the bindings of f that the name can be: their modules end with
        # the modules that the use writes (a binding inside a functor has
        # modules that are not known: it can be any)
        if here is None:
            return False, (
                "the use stands inside a functor or a module type of the file: "
                "the words do not say what %s is there" % u.name
            )
        can_be = [
            (pos, ms)
            for pos, ms in ((pos, rocq_modules(text, spans, pos)) for pos in margin)
            if ms is None or ms[-len(written):] == written
        ]
        if len(can_be) != 1:
            return False, "%d bindings of the file can be %s: the words do not say which the use reaches" % (
                len(can_be),
                u.name,
            )
        binding, modules = can_be[0]
        if modules is None:
            return False, "%s is bound inside a functor or a module type of the file" % f
    else:
        local = [
            m.start()
            for m in re.finditer(r"%slet\s+%s%s" % (ahead, re.escape(f), behind), text)
        ]
        if len(margin) + len(local) != 1:
            return False, "the file binds %s %d times: the words do not say which the use reaches" % (
                f,
                len(margin) + len(local),
            )
        if local:
            return of_a_local(path, text, spans, u, f, local[0])
        binding = margin[0]
        modules = rocq_modules(text, spans, binding)
        if modules is None:
            return False, "%s is bound inside a functor or a module type of the file" % f
        places = may_be_bound(text, f, binding)
        if places:
            return False, (
                "%s also stands where a variable may be bound (line %s): "
                "the words do not say which the use reaches"
                % (f, ", ".join(str(n) for n in places[:5]))
            )
    # the name at the use is the binding only if the use comes after it (or
    # stands in its sentence), nothing is imported between them, and the
    # use stands where the name as it is written is in sight
    first = sentence_at(spans, binding)
    last = sentence_at(spans, u.pos)
    if first == len(spans):
        return False, "no full stop ends the binding of %s" % f
    imported = [a for a, b in spans[first + 1:last] if IMPORTS.match(text, a, b)]
    sight = modules[:len(modules) - len(written)]
    lost = (
        "the use stands before the binding of %s" % f
        if last < first
        else "line %d, between the binding of %s and the use, imports"
        % (text.count("\n", 0, imported[0]) + 1, f)
        if imported
        else "the use stands inside a functor or a module type of the file"
        if here is None
        else "the use stands outside the module of the file where %s is bound" % f
        if here[:len(sight)] != sight
        else None
    )
    if lost:
        return False, "%s: the words do not say what %s is there" % (lost, u.name)
    # Rocq's N bounds the arguments of the OCaml use only if elaboration
    # adds none: no section, no sentence that the tool does not know, and
    # the first N + 1 parameters written in the head of the binding
    end = spans[first][1]
    head = written_head(text, binding + len(f), end)
    other = not_known(text, spans, f)
    added = (
        "a [Section]"
        if in_section(text, spans, binding) or in_section(text, spans, u.pos)
        else "line %d begins with [%s], a sentence that the tool does not know to add none" % other
        if other
        else "the head of the binding of %s, from its name to [:=], is not read: %s" % (f, head[1])
        if head[0] is None
        else "the head of the binding of %s writes %d parameter%s and the use gives %d argument%s: "
        "a parameter that the head does not write is not counted"
        % (f, head[0], "" if head[0] == 1 else "s", u.n, "" if u.n == 1 else "s")
        if head[0] <= u.n
        else None
    )
    if not added:
        added = function_at_the_head(text, head[1], end)
        if added:
            added = "the body of %s: %s" % (f, added)
    if added:
        return False, "Rocq may give %s an argument that is not written (%s)" % (f, added)
    shown, ml = extracted_of(path)
    if ml is None:
        return False, "%s is not there" % shown
    found = extracted_definitions(ml, modules, f)
    inside = ".".join(modules) if modules else "the file"
    if not found:
        return False, "no definition of %s is found among the items of %s in %s" % (f, inside, shown)
    if None in found:
        return False, "the parameters of %s in %s could not be counted" % (f, shown)
    k = min(found)
    why = "%s has %d parameter%s in %s, and is given %d argument%s" % (
        f,
        k,
        "" if k == 1 else "s",
        shown,
        u.n,
        "" if u.n == 1 else "s",
    )
    return k > u.n, why


def main(files):
    bad = 0
    checked = 0
    own = 0
    std = 0
    kept = 0
    by_place = None
    for path in files:
        raw = open(path).read()
        uses, _, errors = analyse(path, raw)
        if errors:
            print("%s: the lint has %d error%s here: run tools/lint.py %s" % (
                path, errors, "" if errors == 1 else "s", path))
            bad += 1
        for line, u in uses:
            if u.verdict is None or u.verdict[0] is None:
                # a function of the file, or of the standard library: the
                # use and its mark
                here = "%s:%d: %s" % (path, line, u.shown)
                if u.verdict is None:
                    own += 1
                    passes, why = of_the_file(path, blank(raw, False), u)
                else:
                    std += 1
                    passes, why = of_the_stdlib(u)
                if passes and u.marked:
                    print("%s has the mark PORT-GAP(papp) and needs none: %s" % (here, why))
                    bad += 1
                elif not passes and u.marked:
                    print("%s keeps its mark PORT-GAP(papp): %s" % (here, why))
                    kept += 1
                elif not passes:
                    print(
                        "%s has no mark PORT-GAP(papp) with [%s] before it, and is not known to run nothing: %s"
                        % (here, u.name, why)
                    )
                    bad += 1
                continue
            if not u.verdict[0] or u.verdict[2] is None:
                continue
            wrapper, _, where, ocaml = TABLE[u.verdict[2]]
            source = where.split(":")[0]
            if wrapper or not source.startswith(SIMPLIFY):
                continue
            extracted = os.path.join(EXTRACTED, source[len(SIMPLIFY):])
            if not os.path.exists(extracted):
                continue
            checked += 1
            name = ocaml.split(".")[-1]
            shown = "extracted/" + source[len(SIMPLIFY):]
            here = "%s:%d: %s" % (path, line, u.shown)
            # the module of the definition in its file: what the rows of the
            # file's own unit say for this place
            if by_place is None:
                by_place = collections.defaultdict(set)
                for _, _, place, o in TABLE.values():
                    by_place[place].add(o)
            unit = os.path.basename(source)[:-3].capitalize()
            modules = sorted(
                tuple(o.split(".")[1:-1])
                for o in by_place[where]
                if o.startswith(unit + ".") and o.split(".")[-1] == name
            )
            if not modules:
                print(
                    "%s: no declared name of %s has the place %s: the module of %s in %s is not known"
                    % (here, unit, where, name, shown)
                )
                bad += 1
                continue
            if len(modules) > 1:
                print(
                    "%s: the declared names of %s give %d modules for the place %s (%s): the module of %s in %s is not known"
                    % (
                        here,
                        unit,
                        len(modules),
                        where,
                        ", ".join(".".join((unit,) + ms) for ms in modules),
                        name,
                        shown,
                    )
                )
                bad += 1
                continue
            text = open(extracted).read()
            found = extracted_definitions(text, modules[0], name)
            inside = ".".join((unit,) + modules[0])
            if not found:
                print(
                    "%s: no definition of %s is found among the items of %s in %s"
                    % (here, name, inside, shown)
                )
                bad += 1
            for k in found:
                if k is None:
                    print(
                        "%s: the parameters of %s in %s could not be counted" % (here, name, shown)
                    )
                    bad += 1
                elif k <= u.n:
                    print(
                        "%s: %s has %d parameter%s in %s, and is given %d argument%s"
                        % (here, name, k, "" if k == 1 else "s", shown, u.n, "" if u.n == 1 else "s")
                    )
                    bad += 1
    print(
        "papp: %d use%s of functions of other ported files of Simplify and %d of functions of the file itself, "
        "compared with the definitions in extracted/, and %d of functions of the standard library, "
        "compared with the definitions in stdlib/: %s"
        % (
            checked,
            "" if checked == 1 else "s",
            own,
            std,
            "%d wrong" % bad
            if bad
            else "each has more parameters than it is given"
            if not kept
            else "%d have more parameters than they are given, %d keep%s the mark"
            % (checked + own + std - kept, kept, "s" if kept == 1 else ""),
        )
    )
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] != "--extracted":
        sys.exit("usage: papp.py --extracted FILE.v ...")
    sys.exit(main(sys.argv[2:]))
