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

"""aliases.py DIR/FILE.v DECL_DIR : prints directives for the extraction of
FILE.v, one a line:

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
- Those that FILE.v itself makes at its left margin, outside any module
  ([Module A := P.]): Rocq prints [module A = P] at that place.
In both cases P must name, perhaps through earlier abbreviations, a module
that DECL_DIR declares outside module types and functors.

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
            if p == opath or p.startswith(opath + "."):
                return spelling + p[len(opath):]
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
    if len(sys.argv) != 3:
        sys.stderr.write(__doc__)
        sys.exit(2)
    v_path, decl_dir = sys.argv[1], sys.argv[2]
    v_text = open(v_path).read()
    rocq = strip_rocq(v_text)
    head = head_block(v_text)
    decl = Decl(decl_dir)
    logical = "SimplifyPort." + re.sub(r"\.v$", "", v_path).lstrip("./").replace("/", ".")

    # (user prefix, OCaml spelling, declared module), in the order of scope
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
                found.append(("SimplifyPort.decl.Simplify_import." + a, a, mod))
        import_env = dict(env)
    else:
        import_env = {}

    # the file's own abbreviations, at its left margin and outside any module
    depth = 0
    env = dict(import_env) if imports else {}
    for line in rocq.split("\n"):
        m = re.match(r"(\s*)Module\s+(Type\s+)?(%s)(.*)$" % NAME, line)
        if m:
            rest = m.group(4).strip()
            m2 = re.match(r":=\s*([A-Za-z0-9_'.]+)\.$", rest)
            if m2 and not m.group(2):
                if depth == 0 and m.group(1) == "":
                    mod = resolve(m2.group(1), env, decl)
                    env[m.group(3)] = mod
                    if mod is not None:
                        found.append((logical + "." + m.group(3), m.group(3), mod))
                continue
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

    for prefix, spelling, mod in found:
        opath = decl.ocaml_path(mod)
        for sub in sorted(decl.constants):
            if sub[: len(mod)] != mod:
                continue
            for kind, name, text in decl.constants[sub]:
                if opath is not None:
                    text = respell(text, opath, spelling)
                ref = ".".join([prefix] + list(sub[len(mod):]) + [name])
                print("%s %s => %s." % (kind, ref, text))


if __name__ == "__main__":
    main()
