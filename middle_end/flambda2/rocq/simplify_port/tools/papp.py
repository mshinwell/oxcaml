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
have the mark PORT-GAP(papp); a use that passes must not.

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
depth; not followed if the file makes two of that name with different
modules) or takes from abbrev/NAME/Port_abbreviations.v; then as it
stands; then under each module that FILE.v imports ([Require Import] of
files of decl/, [Import P.]), the last first. An abbreviation that decl/
makes is followed. What it does not see: a name that Rocq reads otherwise
because a nearer module or variable has the same name. A name with a
module that is not found in the table does not pass.

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
passes, it does not print the lint's errors again (for a file in which the
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
nat}]) is given at every use without being written. Then the extracted
definition has more parameters than the Rocq binding shows, the written N
is too small, and a use that gives the function all its parameters would
pass. So a use of a function of the file is REFUSED unless the words show
that nothing is added:
- neither the binding nor the use stands inside a [Section] (any);
- the binders of the binding, up to its [:] or [:=], are groups in round
  brackets, plain names and [{struct x}]: no [{..}], no [[..]], no
  backquote, nothing else;
- the file has no [Set Implicit Arguments], [Generalizable] or [Existing
  Instance], and no [Arguments] that names the function.
Under these conditions the bound holds, and it is stricter than needed by
what is erased: when this was written the 15 such uses were all [papp1 f
fuel], which in OCaml is the bare name f and runs nothing.

For a DECLARED function (and so for a function of another ported file,
which the use reaches by its declared name) the arguments of the OCaml use
are those that are written: a declaration of decl/ is a [Parameter], which
no section changes, and its only implicit parameters are types, which the
extraction erases. The lint checks that of decl/ (each [{..}] of a
[Parameter] is [{names : Type}]; no [Arguments] names a declared value) and
says so if it is not.

A NAME THAT IS ALSO A VARIABLE. The tool does not follow Rocq's scopes: if
the name f of a function of the file also stands, anywhere in the file,
where a variable may be bound, the use is refused, for a nearer variable f
may be what the use reaches. Where a variable may be bound, as words: from
[fun] to its [=>]; from [forall] or [exists] to the comma; from [let] (and
any word that ends with [!], [*] or [&]: [let!], [let*], [let&],
[let_fuel!], [recursive!]) to its [:=] or [in]; from [fix] to its [:=];
from [with] or a bar to the next [=>] or [:=] (the patterns of a [match],
the binders of a [with]); the word after [as]; in the head of a [match]
after [in] or [return]; after an opening brace up to its [:], bar or [&];
and from the first word of a command (a sentence that begins with a
capital) to its [:=] or its end. The one binding of f itself is not
counted. A use of f elsewhere (after [=>], after [:=], an argument) is no
binder. This reads more as a binder than Rocq does, never less, as far as
the forms above are all the forms that bind.

THE MODULE of a function of the file is that of its binding in FILE.v by
Definition, Fixpoint or [with f (]: the modules that are open there
([Module M.] .. [End M.], as words; a [Section] is no module). For [f]
there must be ONE such binding of f in the whole file. For a name that the
use writes with modules, [X.f], Rocq takes the nearest thing whose name
ENDS with X.f, which need not stand at the root of the file (inside a
module Y it may be Y.X.f). The tool does not follow Rocq's scopes: there
must be ONE binding of f in the whole file whose modules end with X, and
that one is taken, wherever the use stands; if there are several (X.f at
the root and Y.X.f), the use is refused. The use FAILS, closed, for:
- a local function (bound by Rocq's own [let]): the tool does not look
  inside a definition;
- a name that the file binds more than once, or both ways; a name with
  modules that several bindings of the file can be, or none;
- a use with modules that stands inside a functor or a module type of the
  file (there the first module may be the functor's parameter);
- a binding inside a functor or a module type of the file, or under a
  module that is no structure in the extracted text (the application of a
  functor);
- a section, an implicit binder or one of the commands above (elaboration
  may add an argument); the name standing where a variable may be bound;
- no extracted file, no definition found there, parameters that cannot be
  counted, or no more parameters than N (a definition that is another name
  or an application has 0).
A use that fails and has no mark is an error; one that fails and has the
mark is printed ("keeps its mark"); one that passes and has the mark is an
error (the mark is not needed)."""
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


def blank(s, strings):
    """Rocq text with its comments made blank, in the same length. A string
    is made blank too; or, if [strings], keeps its quotes and has x inside."""
    out = []
    depth = 0
    i = 0
    in_str = False
    while i < len(s):
        if depth == 0 and s[i] == '"':
            in_str = not in_str
            out.append('"' if strings else " ")
            i += 1
        elif in_str:
            out.append("\n" if s[i] == "\n" else "x" if strings else " ")
            i += 1
        elif s.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and s.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        else:
            out.append(s[i] if depth == 0 or s[i] == "\n" else " ")
            i += 1
    return "".join(out)


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


def decl_abbreviations():
    """[Module A := P.] of decl/, under the whole name of A. Also fills
    DECL_IMPLICIT: a [Parameter] with a [{..}] that is not [{names :
    Type}], or with a square bracket or a backquote before its text; a
    command [Set Implicit Arguments], [Generalizable], [Existing Instance];
    an [Arguments] that names a lower-case name (a value)."""
    out = {}
    for name in sorted(os.listdir(DECL)):
        if not name.endswith(".v"):
            continue
        stack = [name[:-2]]
        for number, line in enumerate(open(os.path.join(DECL, name)).read().split("\n")):
            s = line.strip()
            if re.match(r"Parameter\s", s):
                braces = re.findall(r"\{[^}]*\}", s)
                if any(not TYPES_ONLY.fullmatch(b) for b in braces) or "`" in s:
                    DECL_IMPLICIT.append("decl/%s:%d" % (name, number + 1))
            elif re.match(
                r"(?:(?:Global|Local|#\[[^\]]*\])\s+)*"
                r"(?:Set\s+Implicit\s+Arguments|Generalizable|Existing\s+Instance"
                r"|Arguments\s+(?:%s\.)*[a-z_])" % PNAME,
                s,
            ):
                DECL_IMPLICIT.append("decl/%s:%d" % (name, number + 1))
            m = re.match(r"Module\s+(?:Type\s+)?(%s)(.*)$" % PNAME, s)
            if m:
                rest = m.group(2).strip()
                a = re.fullmatch(r":=\s*(%s)\." % PPATH, rest)
                if a:
                    out[".".join(stack + [m.group(1)])] = a.group(1)
                elif not re.search(r"\.\s*End\s+%s\.$" % re.escape(m.group(1)), s) and not (
                    ":=" in rest and rest.endswith(".")
                ):
                    stack.append(m.group(1))
                continue
            m = re.match(r"End\s+(%s)\.$" % PNAME, s)
            if m and len(stack) > 1 and stack[-1] == m.group(1):
                stack.pop()
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
# passes, why, the Rocq name in the table), and whether a mark names it.
Use = collections.namedtuple("Use", "pos shown plain n name verdict marked")

PAPP = re.compile(r"(?<![A-Za-z_0-9'])papp([1-4])(?![A-Za-z_0-9'])")
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
    # the abbreviations of the file, and what it imports
    own = collections.defaultdict(set)
    for m in re.finditer(r"(?m)^\s*Module\s+(%s)\s*:=\s*(%s)\.\s*$" % (PNAME, PPATH), text):
        own[m.group(1)].add(m.group(2))
    for m in re.finditer(
        r"(?m)^\s*From\s+SimplifyPort\.abbrev\.(%s)\s+Require\s+Import\s+Port_abbreviations\s*\.\s*$"
        % PNAME,
        text,
    ):
        lib = open(os.path.join(ABBREV, m.group(1), "Port_abbreviations.v")).read()
        for a in re.finditer(
            r"(?m)^Module\s+(%s)\s*:=\s*(%s)\.\s*$" % (PNAME, PPATH), blank(lib, False)
        ):
            if a.group(1) not in own:
                own[a.group(1)].add(a.group(2))
    imports = []
    for m in re.finditer(
        r"(?m)^\s*(?:From\s+SimplifyPort\.decl\s+Require\s+Import\s+([^.]+)\.|Import\s+(%s)\.)\s*$"
        % PPATH,
        text,
    ):
        imports.extend(m.group(1).split() if m.group(1) else [m.group(2)])
    # the modules that the file defines, and the functions that it binds
    defined = set(re.findall(r"(?m)^\s*Module\s+(?:Type\s+)?(%s)" % PNAME, text)) - set(own)
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
        wrapper, definition, where, _ = TABLE[found]
        if wrapper:
            why = "the realisation of %s in decl/ is a function of %d parameters" % (found, wrapper)
            return n < wrapper, why, found
        if definition == "-":
            return False, "%s: %s" % (found, where), found
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
            # of the file (the second step judges that one)
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
                else ("passes" if u.verdict[0] else "does not pass")
                + (" (arguments counted as words)" if u.plain else "")
            )
            why = "" if u.verdict is None else u.verdict[1]
            print("%s:%d\t%s\t%s\t%s" % (path, line_of(u.pos), u.shown, word, why))
        if u.verdict is None or u.verdict[0]:
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


def extracted_definitions(text, modules, name):
    """The numbers of parameters (None: not known) of the definitions of
    [name] among the items of the module [modules] (a list of names; empty
    for the file itself) of an extracted file."""
    definition = re.compile(
        r"(?:let|and)(?:\s*\[@[^\]]*\])*(?:\s+rec(?![A-Za-z0-9_']))?(?:\s*\[@[^\]]*\])*"
        r"\s+%s(?![A-Za-z0-9_'])(.*)$" % re.escape(name)
    )
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
            out.append(count_parameters(" ".join([m.group(1)] + lines[k + 1:k + 8])))
    return out


SENTENCE = re.compile(r"(?m)^[ \t]*(Module\s+Type|Module|Section|End)\s+(%s)([^.]*)\." % PNAME)


def rocq_modules(text, pos):
    """The modules of FILE.v that are open at pos, from the outermost, as
    words; None if one of them is a functor or a module type."""
    stack = []
    for m in SENTENCE.finditer(text, 0, pos):
        kind = " ".join(m.group(1).split())
        if kind == "End":
            if stack and stack[-1][0] == m.group(2):
                stack.pop()
        elif kind == "Section":
            stack.append((m.group(2), "section"))
        elif ":=" in m.group(3):
            pass  # [Module A := P.] is one sentence
        elif kind == "Module Type" or "(" in m.group(3):
            stack.append((m.group(2), None))
        else:
            stack.append((m.group(2), "module"))
    if any(kind is None for _, kind in stack):
        return None
    return [name for name, kind in stack if kind == "module"]


def in_section(text, pos):
    """Whether a [Section] is open at pos, as words."""
    open_sections = []
    for m in SENTENCE.finditer(text, 0, pos):
        kind = " ".join(m.group(1).split())
        if kind == "Section":
            open_sections.append(m.group(2))
        elif kind == "End" and open_sections and open_sections[-1] == m.group(2):
            open_sections.pop()
    return bool(open_sections)


def binders_all_written(text, pos):
    """Whether the binders that follow pos, up to [:] or [:=] outside
    brackets, are only groups in round brackets, plain names and [{struct
    x}]: nothing that Rocq may fill in, and no shape that is not known."""
    i = pos
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ":":
            return True
        elif c == "(":
            i = close_of(text, i, len(text))
            if i is None:
                return False
        elif c == "{":
            j = close_of(text, i, len(text))
            if j is None or not re.fullmatch(r"\{\s*struct\s+%s\s*\}" % PNAME, text[i:j]):
                return False
            i = j
        else:
            m = re.compile(PNAME).match(text, i)
            if not m:
                return False
            i = m.end()
    return False


ADDS_ARGUMENTS = re.compile(
    r"(?m)^[ \t]*(?:(?:Global|Local|#\[[^\]]*\])\s+)*"
    r"(Set\s+Implicit\s+Arguments|Generalizable|Existing\s+Instances?)(?![A-Za-z_0-9'])"
)
TOKEN = re.compile(
    r"\{\||\|\}|\|\||:=|=>|(?P<word>%s[!*&]?)|(?P<end>\.(?=\s|$))|[(){}\[\]]|\S" % PPATH
)


def may_be_bound(text, f, binding):
    """The places (lines) where the word f stands and a variable may be
    bound, as words; the name of the binding at [binding] is not counted."""
    out = []
    depth = 0
    regions = []  # (the tokens that end it, the depth where it began)
    heads = []  # the depths of the [match]es whose [with] has not come
    start = True  # at the first word of a sentence
    after_as = False
    for m in TOKEN.finditer(text):
        t = m.group(0)
        if t in "([{":
            depth += 1
            if t == "{":
                regions.append(((":", "|", "&"), depth))
        elif t in ")]}":
            depth -= 1
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
        if word and t == f and (regions or after_as) and m.start() != binding:
            out.append(text.count("\n", 0, m.start()) + 1)
        after_as = False
        if not word and t != "|":
            continue
        if start and t[0].isupper():
            regions.append(((":=",), depth))
        elif t == "fun":
            regions.append((("=>",), depth))
        elif t in ("forall", "exists", "exists2"):
            regions.append(((",",), depth))
        elif t.startswith("let") or t[-1] in "!*&":
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
        start = False
    return out


def of_the_file(path, text, u):
    """(whether it passes, why) for a use of a function of the file, by
    the file's own extracted text."""
    if u.n is None:
        return False, "its arguments could not be counted"
    parts = u.name.split(".")
    f = parts[-1]
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
    if len(parts) > 1:
        # the bindings of f that the name can be: their modules end with
        # the modules that the use writes (a binding inside a functor has
        # modules that are not known: it can be any)
        written = parts[:-1]
        if rocq_modules(text, u.pos) is None:
            return False, (
                "the use stands inside a functor or a module type of the file: "
                "the words do not say what %s is there" % u.name
            )
        can_be = [
            ms
            for ms in (rocq_modules(text, pos) for pos in margin)
            if ms is None or ms[-len(written):] == written
        ]
        if len(can_be) != 1:
            return False, "%d bindings of the file can be %s: the words do not say which the use reaches" % (
                len(can_be),
                u.name,
            )
        modules = can_be[0]
        if modules is None:
            return False, "%s is bound inside a functor or a module type of the file" % f
        binding = [
            pos
            for pos in margin
            if (rocq_modules(text, pos) or [None])[-len(written):] == written
        ][0]
    else:
        local = re.findall(r"%slet\s+%s%s" % (ahead, re.escape(f), behind), text)
        if local and not margin:
            return False, (
                "%s is a local function (Rocq's own let), which the tool does not look up" % f
            )
        if len(margin) + len(local) != 1:
            return False, "the file binds %s %d times: the words do not say which the use reaches" % (
                f,
                len(margin) + len(local),
            )
        binding = margin[0]
        modules = rocq_modules(text, binding)
        if modules is None:
            return False, "%s is bound inside a functor or a module type of the file" % f
        places = may_be_bound(text, f, binding)
        if places:
            return False, (
                "%s also stands where a variable may be bound (line %s): "
                "the words do not say which the use reaches"
                % (f, ", ".join(str(n) for n in places[:5]))
            )
    # Rocq's N bounds the arguments of the OCaml use only if elaboration
    # adds none
    added = (
        "a [Section]"
        if in_section(text, binding) or in_section(text, u.pos)
        else "a binder of %s that is not written at each use, or that the tool does not know" % f
        if not binders_all_written(text, binding + len(f))
        else "the command [%s]" % " ".join(ADDS_ARGUMENTS.search(text).group(1).split())
        if ADDS_ARGUMENTS.search(text)
        else "an [Arguments] of %s" % f
        if re.search(
            r"(?m)^[ \t]*(?:(?:Global|Local|#\[[^\]]*\])\s+)*Arguments\s+(?:%s\.)*%s(?![A-Za-z_0-9'])"
            % (PNAME, re.escape(f)),
            text,
        )
        else None
    )
    if added:
        return False, "Rocq may give %s an argument that is not written (%s)" % (f, added)
    rel = os.path.relpath(os.path.abspath(path), os.path.abspath(PORT))
    rel = os.path.join(os.path.dirname(rel), os.path.basename(rel)[:-2].lower() + ".ml")
    shown = "extracted/" + rel
    try:
        ml = open(os.path.join(EXTRACTED, rel)).read()
    except IOError:
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
            if u.verdict is None:
                # a function of the file: the use and its mark
                own += 1
                here = "%s:%d: %s" % (path, line, u.shown)
                passes, why = of_the_file(path, blank(raw, False), u)
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
        "compared with the definitions in extracted/: %s"
        % (
            checked,
            "" if checked == 1 else "s",
            own,
            "%d wrong" % bad
            if bad
            else "each has more parameters than it is given"
            if not kept
            else "%d have more parameters than they are given, %d keep%s the mark"
            % (checked + own - kept, kept, "s" if kept == 1 else ""),
        )
    )
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] != "--extracted":
        sys.exit("usage: papp.py --extracted FILE.v ...")
    sys.exit(main(sys.argv[2:]))
