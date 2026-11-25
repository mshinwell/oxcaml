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

gives F its first N arguments only. In OCaml that runs nothing of F when F
is WRITTEN with more than N parameters; the interface does not say so, the
definition does. decl/ARITIES.tsv (made by tools/declgen from the typed
trees of the implementations; decl/README.md, last section) has, for each
declared value, the number of parameters of the function that decl/ writes
as its realisation (0 if the realisation is the name) and the number of
parameters of its definition (- if no definition was read), with the place.
A use PASSES if N is smaller than the first number, or the first number is
0 and N is smaller than the second. A use that does not pass must have the
mark PORT-GAP(papp); a use that passes must not.

Two callers.
- tools/lint.py FILE.v, its fourth check: check(path, raw). With
  LINT_PAPP_ALL in the environment, every use is printed with its verdict.
- papp.py --extracted FILE.v ... (the Makefile's target papp): see THE
  EXTRACTED DEFINITIONS below.

THE MARK of a use is a comment that begins (* PORT-GAP(papp): , stands
before the use in the same definition (up to the full stop that ends a
line), and has the function in square brackets as the use writes it:
[Option.map]. A mark names nothing else in square brackets.

A PARTIAL APPLICATION WITHOUT pappN (a definition that is one: [Definition
print : .. := Code0.print Unit.print.]) is seen only through its mark: when
a mark names F and no [pappN F] follows in the definition, the use is the
first F after the mark, and N is the number of arguments that follow it,
AS WORDS: a name, a number, a string, a group in brackets. If the
application ends with anything but a closing bracket, a full stop, [;] [,]
[|] [:] [=>] or one of [+ * / < > = ++ :: && ||], N is not known and the
mark stays. (A word that is not an argument of F can only make N too
large.) A plain partial application that has NO MARK IS NOT FOUND.

WHICH FUNCTION. It COUNTS WORDS, as tools/lint.py does. The name F is
looked up among the Rocq names of the table: with its first name replaced,
if that is an abbreviation that FILE.v makes ([Module A := P.], at any
depth; not followed if the file makes two of that name with different
modules) or takes from abbrev/NAME/Port_abbreviations.v; then as it
stands; then under each module that FILE.v imports ([Require Import] of
files of decl/, [Import P.]), the last first. An abbreviation that decl/
makes is followed. What it does not see: a name that Rocq reads otherwise
because a nearer module or variable has the same name. NOT CHECKED: a name
without a module, or under a module that FILE.v defines: a function of the
file (the guide wants no mark for it). A name with a module that is not
found in the table does not pass.

THE EXTRACTED DEFINITIONS. The table reads the compiler's files. For a
function of a file of Simplify that is ported, the program that is linked
runs the definition of extracted/DIR/foo.ml instead. So, for each use that
passes by the number of parameters of a definition under
middle_end/flambda2/simplify/, when extracted/ has that file: each
definition of the name at the margin of the file or of a module of it
([let f p1 .. pk =], [and f ..]; also [= fun q -> ..] and [= function]
after it) is found AS WORDS, and must have more parameters than the use
gives arguments. No such definition, or parameters that are not plain
names, is an error that names the use."""
import collections
import os
import re
import sys

PNAME = r"[A-Za-z_][A-Za-z_0-9']*"
PPATH = r"%s(?:\.%s)*" % (PNAME, PNAME)
TOOLS = os.path.dirname(os.path.abspath(__file__))
DECL = os.path.join(TOOLS, "..", "decl")
ABBREV = os.path.join(TOOLS, "..", "abbrev")
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


def decl_abbreviations():
    """[Module A := P.] of decl/, under the whole name of A."""
    out = {}
    for name in sorted(os.listdir(DECL)):
        if not name.endswith(".v"):
            continue
        stack = [name[:-2]]
        for line in open(os.path.join(DECL, name)).read().split("\n"):
            s = line.strip()
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
# as written, and the verdict (None for a function of the file; else
# whether it passes, why, the Rocq name in the table).
Use = collections.namedtuple("Use", "pos shown plain n name verdict")


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

    papps = [
        (m.start(), int(m.group(1)), m.group(2))
        for m in re.finditer(
            r"(?<![A-Za-z_0-9'.])papp([1-4])(?![A-Za-z_0-9'])\s*([^\s()]+|\()", text
        )
    ]
    marks = [m.start() for m in re.finditer(r"\(\*\s*PORT-GAP\(papp\)", raw)]
    if not papps and not marks:
        return [], lines, bad
    if TABLE is None:
        TABLE = read_table()
        IN_DECL = decl_abbreviations()
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
    defined = set(re.findall(r"(?m)^\s*Module\s+(?:Type\s+)?(%s)" % PNAME, text)) - set(own)

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
        if not re.fullmatch(PPATH, f):
            return False, "the function is not written as a name", None
        found = resolve(f)
        if found is None:
            if "." not in f or f.split(".")[0] in defined:
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

    uses = [Use(pos, "papp%d %s" % (n, f), False, n, f, verdict(n, f)) for pos, n, f in papps]
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
                mine = [Use(m.start(), shown, True, n, name, v)]
                uses.append(mine[0])
            failing = [u for u in mine if u.verdict is not None and not u.verdict[0]]
            for u in failing:
                covered.add(u.pos)
            if failing:
                continue
            bad += 1
            if mine[0].verdict is None:
                lines.append("%s names %s, a function of the file: no mark" % (where, name))
            else:
                lines.append(
                    "%s names %s, which needs none: %s: %s"
                    % (where, name, mine[0].shown, mine[0].verdict[1])
                )
    uses.sort(key=lambda u: u.pos)
    for u in uses:
        if os.environ.get("LINT_PAPP_ALL"):
            word = (
                "of the file"
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


PARAMETER = re.compile(r"[a-z_][A-Za-z0-9_']*|\(\)")


def count_parameters(rest):
    """The parameters of [p1 .. pk = BODY], with those of [fun q1 .. ->] and
    of [function] at the head of BODY; None if one is not a plain name."""
    head, eq, body = rest.partition("=")
    if not eq:
        return None
    n = 0
    for w in head.split():
        if not PARAMETER.fullmatch(w):
            return None
        n += 1
    body = body.strip()
    while True:
        if re.match(r"function(?![A-Za-z0-9_'])", body):
            return n + 1
        m = re.match(r"fun\s+([^-]*?)->", body)
        if not m:
            return n
        for w in m.group(1).split():
            if not PARAMETER.fullmatch(w):
                return n
            n += 1
        body = body[m.end():].strip()


def extracted_definitions(text, name):
    """The numbers of parameters of the definitions of [name] at the margin
    of an extracted file or of a module of it."""
    out = []
    lines = text.split("\n")

    def indent(line):
        return len(line) - len(line.lstrip())

    for k, line in enumerate(lines):
        m = re.match(
            r"(\s*)(?:let|and)(?:\s+rec)?\s+%s(?![A-Za-z0-9_'])(.*)$" % re.escape(name), line
        )
        if not m:
            continue
        if m.group(1):
            # inside a module, not inside a definition: the nearest line
            # above with less indentation opens a structure
            j = k - 1
            while j >= 0 and (not lines[j].strip() or indent(lines[j]) >= len(m.group(1))):
                j -= 1
            if j < 0 or not lines[j].rstrip().endswith("struct"):
                continue
        out.append(count_parameters(" ".join([m.group(2)] + lines[k + 1:k + 8])))
    return out


def main(files):
    bad = 0
    checked = 0
    for path in files:
        uses, _, _ = analyse(path, open(path).read())
        for line, u in uses:
            if u.verdict is None or not u.verdict[0] or u.verdict[2] is None:
                continue
            wrapper, _, where, ocaml = TABLE[u.verdict[2]]
            source = where.split(":")[0]
            if wrapper or not source.startswith(SIMPLIFY):
                continue
            extracted = os.path.join(EXTRACTED, source[len(SIMPLIFY):])
            if not os.path.exists(extracted):
                continue
            name = ocaml.split(".")[-1]
            shown = "extracted/" + source[len(SIMPLIFY):]
            here = "%s:%d: %s" % (path, line, u.shown)
            found = extracted_definitions(open(extracted).read(), name)
            checked += 1
            if not found:
                print("%s: no definition of %s is found at the margin of %s" % (here, name, shown))
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
        "papp: %d use%s of functions of the ported files of Simplify, compared with the definitions in extracted/: %s"
        % (checked, "" if checked == 1 else "s", "%d wrong" % bad if bad else "each has more parameters than it is given")
    )
    return 1 if bad else 0


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] != "--extracted":
        sys.exit("usage: papp.py --extracted FILE.v ...")
    sys.exit(main(sys.argv[2:]))
