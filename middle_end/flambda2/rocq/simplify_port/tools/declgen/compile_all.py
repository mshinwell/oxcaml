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

"""compile_all.py [FILE.v ...] : from simplify_port/, compiles the kit and the
files of decl/ (all, or those given and what they require) with Rocq, one
process at a time, in the order of their requirements, in a copy under
_build/declcheck (nothing is written beside the sources). The kit is the
file named by the variable KIT, or monad/real/Port_monad.v, or
Port_monad.v. Only what has changed is compiled again. Prints the first
lines of each failure and a count. Then, when all the files are compiled:
each module of decl/FUNCTOR-ARGUMENTS.tsv is given to a functor of Rocq
whose parameter has the module type of its row, so that Rocq says whether
the module has all that the module type names. This file follows no file of
the compiler."""
import filecmp, os, re, shutil, subprocess, sys

kit = os.environ.get("KIT")
if not kit:
    kit = "monad/real/Port_monad.v" if os.path.exists("monad/real/Port_monad.v") else "Port_monad.v"
work = os.path.join("_build", "declcheck")
os.makedirs(os.path.join(work, "decl"), exist_ok=True)
def bring(src, dst):
    if not os.path.exists(dst) or not filecmp.cmp(src, dst, shallow=False):
        shutil.copyfile(src, dst)
bring(kit, os.path.join(work, "Port_monad.v"))
sources = sorted(f for f in os.listdir("decl") if f.endswith(".v"))
for f in sources:
    bring(os.path.join("decl", f), os.path.join(work, "decl", f))
for f in os.listdir(os.path.join(work, "decl")):
    if f.endswith(".v") and f not in sources:
        for ext in (".v", ".vo", ".glob", ".vos", ".vok"):
            q = os.path.join(work, "decl", f[:-2] + ext)
            if os.path.exists(q):
                os.remove(q)
os.chdir(work)

def requires(path):
    out = []
    for l in open(path):
        m = re.match(r"From SimplifyPort\.decl Require (.*)\.$", l.strip())
        if m:
            out += m.group(1).split()
    return out

files = {f[:-2]: os.path.join("decl", f) for f in os.listdir("decl") if f.endswith(".v")}
want = [os.path.basename(a)[:-2] for a in sys.argv[1:]] or sorted(files)
order, seen = [], set()
def visit(n, stack=()):
    if n in seen:
        return
    if n in stack:
        print("CYCLE: " + " -> ".join(stack + (n,)))
        return
    if n not in files:
        print("MISSING: decl/%s.v (required by %s)" % (n, stack[-1] if stack else "?"))
        seen.add(n)
        return
    for d in requires(files[n]):
        visit(d, stack + (n,))
    seen.add(n)
    order.append(n)
for n in want:
    visit(n)
def run(path):
    return subprocess.run(["rocq", "compile", "-q", "-Q", ".", "SimplifyPort", path],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          universal_newlines=True)
if not os.path.exists("Port_monad.vo") or os.path.getmtime("Port_monad.vo") < os.path.getmtime("Port_monad.v"):
    r = run("Port_monad.v")
    if r.returncode:
        print(r.stderr); sys.exit(1)
bad = 0
failed = set()
made = set()
def fresh(n):
    vo = files[n][:-2] + ".vo"
    if not os.path.exists(vo) or os.path.getmtime(vo) < os.path.getmtime(files[n]):
        return False
    if os.path.getmtime(vo) < os.path.getmtime("Port_monad.vo"):
        return False
    return not any(d in made for d in requires(files[n]))
for n in order:
    if any(d in failed for d in requires(files[n])):
        failed.add(n); bad += 1
        print("SKIPPED %s (a requirement failed)" % n)
        continue
    if fresh(n):
        continue
    made.add(n)
    r = run(files[n])
    if r.returncode:
        bad += 1; failed.add(n)
        print("FAILED %s\n%s" % (n, "\n".join((r.stdout + r.stderr).strip().split("\n")[:6])))
print("%d files, %d compiled now, %d failed or skipped" % (len(order), len(made), bad))

# The modules that the files of Simplify give to their functors: Rocq
# checks that each has all that the module type names, by giving it to a
# functor of Rocq whose parameter has that module type.
table = os.path.join("decl", "FUNCTOR-ARGUMENTS.tsv")
pairs = []
if not sys.argv[1:] and os.path.exists(os.path.join("..", "..", table)):
    for l in open(os.path.join("..", "..", table)):
        c = l.rstrip("\n").split("\t")
        if len(c) == 6 and c[4] and c[5] and (c[4], c[5]) not in pairs:
            pairs.append((c[4], c[5]))
if pairs and not bad:
    types = sorted(set(t for t, _ in pairs))
    units = sorted(set(x.split(".")[0] for pair in pairs for x in pair))
    head = ["From SimplifyPort Require Import Port_monad.",
            "From SimplifyPort.decl Require %s." % " ".join(units)]
    head += ["Module Wants_%d (N : %s). End Wants_%d." % (i, t, i) for i, t in enumerate(types)]
    def given(lines):
        open("Functor_arguments_check.v", "w").write("\n".join(head + lines) + "\n")
        return run("Functor_arguments_check.v")
    line = lambda k: "Module Given_%d := Wants_%d %s." % (k, types.index(pairs[k][0]), pairs[k][1])
    r = given([line(k) for k in range(len(pairs))])
    wrong = 0
    if r.returncode:
        # which ones: each alone
        for k in range(len(pairs)):
            r = given([line(k)])
            if r.returncode:
                wrong += 1
                print("NOT OF ITS MODULE TYPE: %s given where %s is wanted\n%s"
                      % (pairs[k][1], pairs[k][0],
                         "\n".join((r.stdout + r.stderr).strip().split("\n")[:4])))
    print("%d modules given where one of %d module types is wanted: %d do not have what the module type names"
          % (len(pairs), len(types), wrong))
    bad += wrong
sys.exit(1 if bad else 0)
