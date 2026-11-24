#!/usr/bin/env python3
"""check_realisations.py CMI_ROOT : from simplify_port/, checks with OCaml
that what the files of decl/ name exists in the compiler: every realisation
string is an expression (or a type) of OCaml that type-checks against the
compiled interfaces, every constructor of a mirrored variant and every
field of a mirrored record is the compiler's. One line of OCaml for each
thing; the compiler is run once, and once more for each line that it
refuses (one process at a time). Prints what is refused. This file follows
no file of the compiler."""
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


def unq(s):
    return s.replace('""', '"')


for f in sorted(os.listdir("decl")):
    if not f.endswith(".v"):
        continue
    unit = f[:-2]
    mods = [renamed.get(unit, unit)]
    if mods == ["Stdlib"]:
        mods = []
    last_is_type = False
    arity = {}
    lines = open(os.path.join("decl", f)).read().split("\n")
    i = 0
    while i < len(lines):
        l = lines[i].strip()
        where = "decl/%s:%d" % (f, i + 1)
        m = re.match(r"Module (\w+)\.$", l)
        if m:
            mods.append(renamed.get(m.group(1), m.group(1)))
        elif re.match(r"End (\w+)\.$", l):
            mods.pop()
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
        i += 1

out = os.path.join("_build", "declgen", "check")
os.makedirs(out, exist_ok=True)
src = os.path.join(out, "realisations.ml")
text = [c for _, c in checks]
refused = []
private = 0
while True:
    open(src, "w").write("\n".join(text) + "\n")
    r = subprocess.run(["ocamlc.opt", "-c", "-nolabels", "-w", "-a"] + inc + opens + ["-o",
                       os.path.join(out, "realisations.cmo"), src],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    if r.returncode == 0:
        break
    m = re.search(r"line (\d+)", r.stderr)
    if not m:
        print(r.stderr)
        sys.exit(2)
    n = int(m.group(1)) - 1
    err = " ".join(x.strip() for x in r.stderr.strip().split("\n")[1:])[:300]
    if "(constructor)" in checks[n][0] and "private type" in r.stderr:
        private += 1
    else:
        refused.append((checks[n][0], checks[n][1], err))
    text[n] = ""
    if len(refused) + private > 600:
        break
for where, line, err in refused:
    print("%s\n    %s\n    %s" % (where, line[:200], err))
print("%d things checked, %d refused by OCaml (and %d makers of private types, which the port does not use)"
      % (len(checks), len(refused), private))
sys.exit(1 if refused else 0)
