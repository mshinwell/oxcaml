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

"""aliases.py DIR/FILE.v DECL_DIR [ABBREV_DIR] : prints directives for the
extraction of FILE.v, one a line:

    Extract Inlined Constant REF => "TEXT".
    Extract Inductive REF => "TEXT" [ "TEXT" ... ].

WHY. Rocq keeps the OCaml text of a declared name under the name by which
the Rocq file REACHES it. A name reached through an abbreviation of a module
([UA.uenv], where [Module UA := Upwards_acc.]) has no text of its own: Rocq
prints the module's full name and the Rocq name of the constant
([Upwards_acc.uenv]), and does not look at the text that decl/ gives for
[Upwards_acc.uenv]. The directives printed here give each such name its
text: the text of decl/, with the module's path written as the abbreviation.
So the extracted file says [UA.uenv] where the Rocq file says [UA.uenv] and
[Upwards_acc.uenv] where it says that, as the compiler's file does; and a
text of decl/ that is not the bare name (a wrapper for an optional argument,
a renamed name) is used through an abbreviation too.

WHICH ABBREVIATIONS.
- Those of DECL_DIR/Simplify_import.v ([Module A := P.]), when FILE.v says
  [Require Import ... Simplify_import] AND the OCaml text that it carries at
  its head (between "(*OCAML" and "OCAML*)") has [open Simplify_import] or
  [open! Simplify_import]: the extracted file then has the same
  abbreviations, from the extracted Simplify_import. One of them is left
  out if that OCaml text binds a module of its name.
- Those of a library ABBREV_DIR/NAME/Port_abbreviations.v ([Module A :=
  P.]) that FILE.v takes by [From SimplifyPort.abbrev.NAME Require Import
  Port_abbreviations.]: the abbreviations that the compiler's file makes
  itself. Rocq prints no line [module A = P] for them, so the OCaml head of
  FILE.v must have, for each, the line [module A = P'] at its left margin,
  and P' must be the same module as P: the tool stops with an error if it
  is not so. (An abbreviation that FILE.v makes itself, next kind, has a
  cost: for it Rocq writes down the names of the whole module, and then
  gives a number to each variable of the file that has one of those names.)
- Those that FILE.v itself makes at its left margin, outside any module
  ([Module A := P.]): Rocq prints [module A = P] at that place.
In all cases P must name, perhaps through earlier abbreviations, a module
that DECL_DIR declares outside module types and functors.

WHERE ROCQ CHOOSES THE NAME (the type of a matched value, as decl/ wrote it:
whole). The whole name of a declared constant or inductive type gets the
abbreviation too, when (1) FILE.v writes that constant, or that type or a
constructor of it, with exactly one abbreviation, (2) FILE.v never writes it
whole, and (3) the abbreviation holds in the whole extracted file: it is
one of Simplify_import or of the library of ABBREV_DIR and FILE.v binds no
module or functor parameter of that name; or FILE.v makes it before its
first definition and binds the name once. A module that FILE.v opens ([Import P.] before its first
definition, with [open P] or [open! P] in its OCaml head) counts here as
an abbreviation that is empty: a name of a module inside P is then written
without P, if the file binds no module of that first name.

THE TEXT. For a constant or an inductive type of that module, or of a module
inside it: the text of DECL_DIR, in which each path that begins with the
OCaml name of the module has [A] in the place of that beginning. (The OCaml
name of the module is read from the texts of its constants; if they do not
agree on one, the text is that of DECL_DIR unchanged.)

It follows no file of the compiler.
"""
import collections
import os
import re
import sys

NAME = r"[A-Za-z_][A-Za-z0-9_']*"
OPATH = r"[A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*"
TOKEN = re.compile(
    r"(?<![A-Za-z0-9_'.])(%s)\.([a-z_][A-Za-z0-9_']*|\( [^ ]+ \))(?![A-Za-z0-9_'])" % OPATH
)


def strip_rocq(s):
    """Rocq text with its comments and strings made blank."""
    out = []
    i = 0
    depth = 0
    in_str = False
    while i < len(s):
        if depth == 0 and s[i] == '"':
            in_str = not in_str
            out.append(" ")
            i += 1
            continue
        if in_str:
            out.append("\n" if s[i] == "\n" else " ")
            i += 1
            continue
        if s.startswith("(*", i):
            depth += 1
            i += 2
            out.append("  ")
            continue
        if depth and s.startswith("*)", i):
            depth -= 1
            i += 2
            out.append("  ")
            continue
        out.append(s[i] if depth == 0 or s[i] == "\n" else " ")
        i += 1
    return "".join(out)


def head_block(v_text):
    lines = []
    on = False
    for line in v_text.split("\n"):
        if line == "(*OCAML":
            on = True
            continue
        if line == "OCAML*)":
            on = False
            continue
        if on:
            lines.append(line)
    return lines


class Decl:
    """What DECL_DIR declares outside module types and functors: for each
    module (a tuple of Rocq names, the file first) its constants with their
    OCaml text, the modules inside it, and its abbreviations."""

    def __init__(self, decl_dir):
        self.constants = collections.defaultdict(list)  # module -> [(name, text)]
        self.modules = set()
        self.aliases = collections.defaultdict(list)  # file -> [(name, target)]
        for name in sorted(os.listdir(decl_dir)):
            if name.endswith(".v"):
                self._read(os.path.join(decl_dir, name), name[:-2])

    def _read(self, path, file_module):
        stack = [file_module]
        self.modules.add((file_module,))
        skip = 0
        for line in open(path).read().split("\n"):
            s = line.strip()
            m = re.match(r"Module\s+(Type\s+)?(%s)(.*)$" % NAME, s)
            if m:
                rest = m.group(3).strip()
                m2 = re.match(r":=\s*([A-Za-z0-9_'.]+)\.$", rest)
                if m2 and not m.group(1):
                    if not skip and len(stack) == 1:
                        self.aliases[file_module].append((m.group(2), m2.group(1)))
                    continue
                if ":=" in rest and rest.endswith("."):
                    continue
                if skip or m.group(1) or "(" in rest:
                    skip += 1
                stack.append(m.group(2))
                if not skip:
                    self.modules.add(tuple(stack))
                continue
            m = re.match(r"End\s+(%s)\.$" % NAME, s)
            if m and len(stack) > 1 and stack[-1] == m.group(1):
                stack.pop()
                if skip:
                    skip -= 1
                continue
            if skip:
                continue
            m = re.match(r'(Extract Inlined Constant|Extract Inductive)\s+(%s)\s*=>\s*(".*)\.$' % NAME, s)
            if m:
                self.constants[tuple(stack)].append((m.group(1), m.group(2), m.group(3)))

    def ocaml_path(self, module):
        """The OCaml path of a declared module, read from the texts of its
        constants and of the modules inside it: None if they do not agree."""
        found = set()
        for mod, consts in self.constants.items():
            if mod[: len(module)] != module:
                continue
            extra = len(mod) - len(module)
            for kind, _, text in consts:
                if kind != "Extract Inlined Constant":
                    continue
                toks = TOKEN.findall(text[1:-1].replace('""', '"'))
                if len(toks) != 1:
                    continue
                parts = toks[0][0].split(".")
                if len(parts) <= extra:
                    return None
                found.add(".".join(parts[: len(parts) - extra]))
        return found.pop() if len(found) == 1 else None


def respell(text, opath, spelling):
    """The Rocq strings of TEXT with each path that begins with the module
    OPATH written with SPELLING in its place."""

    def in_string(m):
        def one(t):
            p = t.group(0)
            if spelling and (p == opath or p.startswith(opath + ".")):
                return spelling + p[len(opath):]
            if not spelling and p.startswith(opath + "."):
                return p[len(opath) + 1:]
            return p

        return re.sub(r"(?<![A-Za-z0-9_'.])%s" % OPATH, one, m.group(0))

    return re.sub(r'"(?:[^"]|"")*"', in_string, text)


def resolve(target, env, decl):
    """A Rocq path of an abbreviation, to a declared module or None."""
    target = re.sub(r"^(SimplifyPort\.)?decl\.", "", target)
    parts = target.split(".")
    if parts[0] in env:
        if env[parts[0]] is None:
            return None
        mod = env[parts[0]] + tuple(parts[1:])
    else:
        mod = tuple(parts)
    return mod if mod in decl.modules else None


def main():
    if len(sys.argv) not in (3, 4):
        sys.stderr.write(__doc__)
        sys.exit(2)
    v_path, decl_dir = sys.argv[1], sys.argv[2]
    abbrev_dir = sys.argv[3] if len(sys.argv) == 4 else None
    v_text = open(v_path).read()
    rocq = strip_rocq(v_text)
    head = head_block(v_text)
    decl = Decl(decl_dir)
    logical = "SimplifyPort." + re.sub(r"\.v$", "", v_path).lstrip("./").replace("/", ".")

    # (user prefix, OCaml spelling, declared module, line or None), in the
    # order of scope
    found = []

    imports = False
    for m in re.finditer(r"^(?:From\s+SimplifyPort\.decl\s+)?Require\s+Import\s+([^.]*(?:\.[A-Za-z][^.]*)*)\.\s*$", rocq, re.M):
        if re.search(r"(?<![A-Za-z0-9_'.])Simplify_import(?![A-Za-z0-9_'])", m.group(1)):
            imports = True
    opened = any(re.match(r"open!?\s+Simplify_import\s*$", l) for l in head)
    head_binds = set()
    for l in head:
        m = re.match(r"\s*module\s+(?:type\s+)?(%s)" % NAME, l)
        if m:
            head_binds.add(m.group(1))
    if imports and opened:
        env = {}
        for a, target in decl.aliases["Simplify_import"]:
            mod = resolve(target, env, decl)
            env[a] = mod
            if mod is not None and a not in head_binds:
                found.append(("SimplifyPort.decl.Simplify_import." + a, a, mod, None))
        import_env = dict(env)
    else:
        import_env = {}

    # the library of the file's own abbreviations
    own_env = {}
    m = re.search(r"^From\s+SimplifyPort\.abbrev\.(%s)\s+Require\s+Import\s+Port_abbreviations\.\s*$" % NAME, rocq, re.M)
    if m and abbrev_dir is not None:
        lib = m.group(1) + ".Port_abbreviations"
        a_text = strip_rocq(open(os.path.join(abbrev_dir, m.group(1), "Port_abbreviations.v")).read())
        env = {}
        if re.search(r"Require\s+Import\s+[^.]*(?<![A-Za-z0-9_'.])Simplify_import(?![A-Za-z0-9_'])", a_text):
            for a, target in decl.aliases["Simplify_import"]:
                env[a] = resolve(target, env, decl)
        # what the OCaml head binds, with the paths written out
        ml = collections.OrderedDict()
        if opened:
            text = open(os.path.join(decl_dir, "Simplify_import.v")).read()
            for mm in re.finditer(r"\(\* module (%s) = (%s) \*\)" % (OPATH, OPATH), text):
                parts = mm.group(2).split(".")
                ml[mm.group(1)] = ".".join(ml.get(parts[0], parts[0]).split(".") + parts[1:])
        for l in head:
            mm = re.match(r"module\s+(%s)\s*=\s*(%s)\s*$" % (NAME, OPATH), l)
            if mm:
                parts = mm.group(2).split(".")
                ml[mm.group(1)] = ".".join(ml.get(parts[0], parts[0]).split(".") + parts[1:])
        bad = 0
        for mm in re.finditer(r"^Module\s+(%s)\s*:=\s*([A-Za-z0-9_'.]+)\.\s*$" % NAME, a_text, re.M):
            a = mm.group(1)
            mod = resolve(mm.group(2), env, decl)
            env[a] = mod
            if mod is None:
                continue
            want = decl.ocaml_path(mod)
            if want is None:
                want = ".".join(c[:-1] if c.endswith("_") else c for c in mod)
            if ml.get(a) != want or not any(
                re.match(r"module\s+%s\s*=" % re.escape(a), l) for l in head
            ):
                sys.stderr.write(
                    "%s: the abbreviation %s of %s is the module %s, but the OCaml "
                    "head of the file has %s\n"
                    % (v_path, a, lib, want, "module %s = %s" % (a, ml[a]) if a in ml else "no line for it")
                )
                bad += 1
                continue
            found.append(("SimplifyPort.abbrev.%s.%s" % (lib, a), a, mod, None))
        if bad:
            sys.exit(1)
        own_env = env

    # the file's own abbreviations, at its left margin and outside any module
    depth = 0
    env = dict(import_env) if imports else {}
    env.update(own_env)
    bound = collections.Counter()  # every module name that the file binds
    first_def = None  # the line of the first definition or module of the file
    lines = rocq.split("\n")
    for i, line in enumerate(lines):
        if first_def is None and re.match(
            r"(Definition|Fixpoint|Inductive|Record|Variant|Parameter|Axiom|Section|Notation|Extract)(?![A-Za-z0-9_'])", line
        ):
            first_def = i
        m = re.match(r"(\s*)Module\s+(Type\s+)?(%s)(.*)$" % NAME, line)
        if m:
            rest = m.group(4).strip()
            bound[m.group(3)] += 1
            for b in re.findall(r"\(\s*((?:%s\s+)*%s)\s*:" % (NAME, NAME), rest):
                for x in b.split():
                    bound[x] += 1
            m2 = re.match(r":=\s*([A-Za-z0-9_'.]+)\.$", rest)
            if m2 and not m.group(2):
                if depth == 0 and m.group(1) == "":
                    mod = resolve(m2.group(1), env, decl)
                    env[m.group(3)] = mod
                    if mod is not None:
                        found.append((logical + "." + m.group(3), m.group(3), mod, i))
                continue
            if first_def is None:
                first_def = i
            if ":=" in rest and rest.rstrip().endswith("."):
                if depth == 0:
                    env[m.group(3)] = None
                continue
            if depth == 0:
                env[m.group(3)] = None
            depth += 1
            continue
        if re.match(r"\s*End\s+%s\.\s*$" % NAME, line) and depth:
            depth -= 1
    if first_def is None:
        first_def = len(lines)

    for prefix, spelling, mod, _ in found:
        opath = decl.ocaml_path(mod)
        for sub in sorted(decl.constants):
            if sub[: len(mod)] != mod:
                continue
            for kind, name, text in decl.constants[sub]:
                if opath is not None:
                    text = respell(text, opath, spelling)
                ref = ".".join([prefix] + list(sub[len(mod):]) + [name])
                print("%s %s => %s." % (kind, ref, text))

    # WHERE ROCQ CHOOSES THE NAME: the whole name of a declared thing gets
    # the abbreviation too, if the file writes that thing with one
    # abbreviation only, never whole, and the abbreviation holds in the
    # whole extracted file.
    tokens = collections.Counter(
        re.findall(r"(?<![A-Za-z0-9_'.])(%s(?:\.%s)+)" % (NAME, NAME), rocq)
    )
    everywhere = []
    for prefix, spelling, mod, line in found:
        if line is None:
            ok = bound[spelling] == 0
        else:
            ok = line < first_def and bound[spelling] == 1
        if ok:
            everywhere.append((spelling, mod))
    # a module that the file opens, in Rocq ([Import P.] before the first
    # definition) and in the OCaml text of its head ([open P]): the empty
    # abbreviation
    head_opens = set()
    for l in head:
        m = re.match(r"open!?\s+(%s)\s*$" % OPATH, l)
        if m:
            head_opens.add(m.group(1))
    for i, line in enumerate(lines[:first_def]):
        m = re.match(r"Import\s+([A-Za-z0-9_'. ]+)\.\s*$", line)
        if not m:
            continue
        for target in m.group(1).split():
            mod = tuple(re.sub(r"^(SimplifyPort\.)?decl\.", "", target).split("."))
            if mod in decl.modules and decl.ocaml_path(mod) in head_opens:
                everywhere.append(("", mod))
    for sub in sorted(decl.constants):
        for kind, name, text in decl.constants[sub]:
            names = [name]
            if kind == "Extract Inductive":
                for c in re.findall(r'"((?:[^"]|"")*)"', text)[1:]:
                    if re.fullmatch(OPATH, c):
                        names.append(c.split(".")[-1])
            whole = ".".join(sub)
            if any(tokens[whole + "." + n] or tokens["decl." + whole + "." + n] for n in names):
                continue
            used = set()
            for spelling, mod in everywhere:
                if sub[: len(mod)] != mod:
                    continue
                if spelling:
                    short = ".".join([spelling] + list(sub[len(mod):]))
                else:
                    # an opened module: the name of a module inside it,
                    # which nothing of the file may bind
                    if len(sub) == len(mod):
                        continue
                    first = sub[len(mod)]
                    if bound[first] or first in head_binds or first.endswith("_"):
                        continue
                    short = ".".join(sub[len(mod):])
                if any(tokens[short + "." + n] for n in names):
                    used.add((spelling, mod))
            if len(used) != 1:
                continue
            spelling, mod = used.pop()
            opath = decl.ocaml_path(mod)
            if opath is None:
                continue
            ref = ".".join(["SimplifyPort.decl"] + list(sub) + [name])
            print("%s %s => %s." % (kind, ref, respell(text, opath, spelling)))


if __name__ == "__main__":
    main()
