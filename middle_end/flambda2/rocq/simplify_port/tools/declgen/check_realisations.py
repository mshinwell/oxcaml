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

"""check_realisations.py CMI_ROOT : from simplify_port/, checks with OCaml
that what the files of decl/ name exists in the compiler: every realisation
string is an expression (or a type) of OCaml that type-checks against the
compiled interfaces, every constructor of a mirrored variant and every
field of a mirrored record is the compiler's. One line of OCaml for each
thing; the compiler is run once, and once more for each line that it
refuses (one process at a time). It does not compare the type that OCaml
gives a realisation with the signature that Rocq has for it.

Prints what OCaml refuses; then the number of things that OCaml checked;
then, apart, what was not checked, with numbers and reasons: the
constructor functions of private types, and what is declared of a module
local to a file when its definition cannot be checked apart from the file.
This file follows no file of the compiler."""
import os, re, subprocess, sys

cmi_root = sys.argv[1]
S = os.path.join(cmi_root, "middle_end", "flambda2")
inc = []
for d in [".ocamlcommon.objs/byte", ".oxcaml_common.objs/byte", ".ocamlfrontend.objs/byte",
          ".ocamlbytecomp.objs/byte", ".ocamloptcomp.objs/byte",
          "backend/debug/dwarf/dwarf_flags/.dwarf_flags.objs/byte",
          "middle_end/flambda2/numbers/floats/.flambda2_floats.objs/byte"]:
    inc += ["-I", os.path.join(cmi_root, d)]
for d in ("algorithms bound_identifiers classic_mode_types cmx compare datalog from_lambda "
          "identifiers import kinds lattices nominal numbers parser reaper simplify "
          "simplify_shared term_basics terms to_cmm to_jsir types ui").split():
    p = os.path.join(S, d, ".flambda2_%s.objs" % d, "byte")
    if os.path.isdir(p):
        inc += ["-I", p]
opens = []
for l in ("algorithms bound_identifiers cmx identifiers kinds lattices numbers nominal "
          "term_basics terms simplify_shared types ui simplify").split():
    opens += ["-open", "Flambda2_" + l]

renamed = {"Variable_": "Variable", "Stdlib_": "Stdlib", "Set_": "Set", "Import_": "Import",
           "Export_": "Export"}
checks = []  # (where, line of OCaml)
# For a unit FILE__local: the definition of each module is copied from the
# file, and what is declared of it is checked beside it, inside one module
# of the test. group[i]: the number of that module for the check i, or None.
group = {}
prelude = set()
source_root = os.path.join("..", "..", "..", "..")
ngroups = 0
# What is not checked: (file of decl/, reason) -> number of things.
skipped = {}


def skip(where, reason, n):
    f = where.split(":")[0]
    skipped[(f, reason)] = skipped.get((f, reason), 0) + n


def unq(s):
    return s.replace('""', '"')


for f in sorted(os.listdir("decl")):
    if not f.endswith(".v"):
        continue
    unit = f[:-2]
    mods = [renamed.get(unit, unit)]
    if mods == ["Stdlib"]:
        mods = []
    local = unit.endswith("__local")
    local_source = None
    cur_group = None
    depth = 0
    if local:
        mods = []
    last_is_type = False
    arity = {}
    lines = open(os.path.join("decl", f)).read().split("\n")
    i = 0
    while i < len(lines):
        l = lines[i].strip()
        where = "decl/%s:%d" % (f, i + 1)
        before = len(checks)
        group_before = cur_group if (cur_group is not None and cur_ok) else None
        # a module type has nothing to check: to its end
        mt = re.match(r"Module Type (\w+)\.$", l)
        if mt:
            end = lines[i][:len(lines[i]) - len(lines[i].lstrip())] + "End %s." % mt.group(1)
            while lines[i] != end:
                i += 1
            i += 1
            continue
        m = re.match(r"Module (\w+)\.$", l)
        if local and local_source is None and l.endswith(".ml"):
            local_source = l.strip()
        if local and l.startswith("(* module ") and "of the file" in l:
            m2 = re.match(r"\(\* module (\w+), lines (\d+)-(\d+) of the file \*\)", l)
            src = open(os.path.join(source_root, local_source)).read().split("\n")
            ngroups += 1
            cur_group = ngroups
            # only a module at the top of the file can be read apart
            cur_ok = len(mods) == 0
            if cur_ok:
                checks.append((where, "module Check_%d = struct" % cur_group))
                prelude.add(len(checks) - 1); group[len(checks) - 1] = cur_group
                for x in src[int(m2.group(2)) - 1:int(m2.group(3))]:
                    checks.append((where, x))
                    prelude.add(len(checks) - 1); group[len(checks) - 1] = cur_group
            depth = 0
        elif m:
            mods.append(renamed.get(m.group(1), m.group(1)))
            depth += 1
        elif re.match(r"End (\w+)\.$", l):
            mods.pop()
            depth -= 1
            if local and cur_group is not None and depth == 0:
                if cur_ok:
                    checks.append((where, "end"))
                    prelude.add(len(checks) - 1); group[len(checks) - 1] = cur_group
                cur_group = None
        elif l.startswith("Parameter "):
            last_is_type = re.search(r": (Type -> )*Type\.$", l) is not None
        elif l.startswith("Definition "):
            last_is_type = ": Type :=" in l
        elif l.startswith("Extract Inlined Constant "):
            m = re.match(r'Extract Inlined Constant \S+ => "(.*)"\.$', l)
            s = unq(m.group(1))
            if last_is_type:
                checks.append((where, "let _ = fun (x : %s) -> x" % s))
            else:
                checks.append((where, "let _ = %s" % s))
        elif l.startswith("Extract Constant "):
            m = re.match(r'Extract Constant \S+ ((?:"[^"]*" )*)=> "(.*)"\.$', l)
            vs = re.findall(r'"([^"]*)"', m.group(1))
            checks.append((where, "let _ = fun (x : %s) -> x" % unq(m.group(2))))
        elif l.startswith("Record "):
            m = re.match(r"Record (\S+).*:= \{ (.*) \}\.$", l)
            fields = [x.split(" : ")[0].strip() for x in m.group(2).split("; ")]
            path = ".".join(mods)
            dot = path + "." if path else ""
            for x in fields:
                checks.append((where, "let _ = fun x -> x.%s%s" % (dot, x)))
        elif l.startswith("Inductive ") or l.startswith("with "):
            m = re.match(r"(?:Inductive|with) (\S+)((?: \(\w+ : Type\))*) : Type :=", l)
            arity[m.group(1)] = m.group(2).count(": Type")
        elif l.startswith("Extract Inductive "):
            m = re.match(r'Extract Inductive (\S+) => "([^"]*)" \[ (.*) \](?: "(.*)")?\.$', l)
            name, ty, ctors, match = m.group(1), m.group(2), m.group(3), m.group(4)
            n = arity.get(name, 0)
            args = "" if n == 0 else "(%s) " % ", ".join("_" for _ in range(n))
            checks.append((where, "let _ = fun (x : %s%s) -> x" % (args, ty)))
            for c in re.findall(r'"([^"]*)"', ctors):
                if c.startswith("("):
                    # refused for a private type, which the port does not build
                    checks.append((where + " (constructor)", "let _ = %s" % c))
                else:
                    checks.append((where, "let _ = function %s _ -> () | _ -> ()" % c))
            if match:
                checks.append((where, "let _ = %s" % match))
            if ty.startswith("(") and match:
                # a tuple with labels: its two functions make and take the
                # type that the directive names
                c = re.findall(r'"([^"]*)"', ctors)[0]
                checks.append((where, "let _ = fun x__ -> (%s x__ : %s)" % (c, ty)))
                checks.append((where, "let _ = fun f__ (x__ : %s) -> %s f__ x__" % (ty, match)))
        if local:
            group_now = cur_group if (cur_group is not None and cur_ok) else group_before
            if group_now is not None:
                for n in range(before, len(checks)):
                    group.setdefault(n, group_now)
            elif len(checks) > before:
                skip(where, "the module is inside another module of its file: its "
                     "definition is not copied", len(checks) - before)
                del checks[before:]
        i += 1

out = os.path.join("_build", "declgen", "check")
os.makedirs(out, exist_ok=True)
src = os.path.join(out, "realisations.ml")
text = [c for _, c in checks]
refused = []
private = 0
accepted_or_refused = len(checks) - len(prelude)
# first each copied definition alone: one that does not stand apart from
# its file is left out, with what is declared of it
for g in sorted(set(group.values())):
    members = sorted(k for k in group if group[k] == g)
    own = [text[k] for k in members if k in prelude]
    probe = os.path.join(out, "definition.ml")
    open(probe, "w").write("\n".join(own) + "\n")
    r = subprocess.run(["ocamlc.opt", "-c", "-nolabels", "-w", "-a"] + inc + opens + ["-o",
                       os.path.join(out, "definition.cmo"), probe],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    if r.returncode != 0:
        err = " ".join(x.strip() for x in r.stderr.strip().split("\n")[1:])[:160]
        n = sum(1 for k in members if k not in prelude)
        skip(checks[members[0]][0], "the definition of the module, copied from the file, "
             "does not compile apart from it (%s)" % err, n)
        accepted_or_refused -= n
        for k in members:
            text[k] = ""
while True:
    open(src, "w").write("\n".join(text) + "\n")
    r = subprocess.run(["ocamlc.opt", "-c", "-nolabels", "-w", "-a"] + inc + opens + ["-o",
                       os.path.join(out, "realisations.cmo"), src],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    if r.returncode == 0:
        break
    m = re.search(r'realisations\.ml", lines? (\d+)', r.stderr)
    if not m:
        print(r.stderr)
        sys.exit(2)
    n = int(m.group(1)) - 1
    if n >= len(checks) or n in prelude:
        # cannot be: each copied definition was compiled alone before
        print(r.stderr)
        sys.exit(2)
    err = " ".join(x.strip() for x in r.stderr.strip().split("\n")[1:])[:300]
    if "(constructor)" in checks[n][0] and "private type" in r.stderr:
        private += 1
        skip(checks[n][0], "a constructor function of a private type, which OCaml "
             "refuses and the port does not use", 1)
        accepted_or_refused -= 1
    else:
        refused.append((checks[n][0], checks[n][1], err))
    text[n] = ""
    if len(refused) + private > 600:
        break
for where, line, err in refused:
    print("%s\n    %s\n    %s" % (where, line[:200], err))
print("%d things checked by OCaml: %d taken, %d refused"
      % (accepted_or_refused, accepted_or_refused - len(refused), len(refused)))
total = sum(skipped.values())
print("%d things not checked:" % total)
by_reason = {}
for (f, reason), n in sorted(skipped.items()):
    by_reason.setdefault(reason, []).append((f, n))
for reason, l in sorted(by_reason.items()):
    print("  %d: %s" % (sum(n for _, n in l), reason))
    if not reason.startswith("a constructor function"):
        for f, n in l:
            print("      %s: %d" % (f, n))
sys.exit(1 if refused else 0)
