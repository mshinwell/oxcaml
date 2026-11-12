#!/usr/bin/env python3
"""Check a tree after C4-heap-sweep.py without stopping at the first
proof that fails, and repair proofs by rules that the error messages
drive. [rocq] must be on the path. Run from anywhere; the tree is the
checkout this file is in, or --root DIR; what it writes goes to the
current directory, or --out DIR.

  suggest         to be run first, on the tree BEFORE the sweep (after
                  [vos]): asks Rocq which variables of its section each
                  proof uses ([Suggest Proof Using]) and writes
                  suggest.json. A proof that is not run is then admitted
                  with those variables, so that a lemma of a section is
                  the same lemma after the section.
  vos             statements only (rocq compile -vos), in dependency
                  order, in parallel. Lists the files that fail and
                  those that wait for them (vos.tsv).
  vok [FILE...]   proofs (rocq compile -vok), each file on its own, in
                  parallel. A proof that fails is recorded and admitted
                  in a copy of the file, and the file is checked again,
                  until it passes: so one failure hides no other.
                  Writes broken.tsv and files.tsv. The sources are not
                  changed.
  vok --repair [FILE...]
                  the same, and each failing proof is given to the
                  rules ([candidates] below): an edit is kept when the
                  proof then passes or its first error moves forward.
                  The edits are made in the sources and listed in
                  repairs.tsv.

The order of a run: [vos], [suggest] on the tree before the sweep; the
sweep; [vos]; [vok --repair]; what broken.tsv then lists is for a hand.
"""
import concurrent.futures as cf
import os
import re
import subprocess
import sys
import threading
import time


def option(name, default):
    if name in sys.argv:
        i = sys.argv.index(name)
        value = sys.argv[i + 1]
        del sys.argv[i:i + 2]
        return value
    return default


R = os.path.abspath(option("--root", os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "..")))
S = os.path.abspath(option("--out", "."))
ENV = dict(os.environ)
LIBS = [
    ("rocq", "OxCamlStdlib"),
    ("backend/rocq", "OxCamlBackend"),
    ("backend/ssa/rocq", "OxCamlSsa"),
    ("backend/ssa/loop/rocq", "OxCamlLoop"),
    ("middle_end/flambda2/rocq", "OxCamlFlambda2"),
    ("middle_end/flambda2/types/rocq", "OxCamlFlambda2Types"),
]
FLAGS = []
for d, lib in LIBS:
    FLAGS += ["-Q", os.path.join(R, d), lib]
SWEPT = [os.path.join(R, "middle_end/flambda2/rocq"),
         os.path.join(R, "middle_end/flambda2/types/rocq")]
JOBS = int(os.environ.get("JOBS", "40"))
TIMEOUT = int(os.environ.get("TIMEOUT", "2400"))


def sources():
    out = []
    for d in SWEPT:
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".v") and "Extract" not in fn and \
                    "__chk" not in fn and "__one" not in fn:
                out.append(os.path.join(d, fn))
    return out


def dependencies(files):
    """file -> the files of [files] that it requires."""
    p = subprocess.run(["rocq", "dep"] + FLAGS + files, env=ENV,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       universal_newlines=True)
    deps = {f: set() for f in files}
    fset = set(files)
    for line in p.stdout.splitlines():
        if ":" not in line:
            continue
        left, right = line.split(":", 1)
        targets = left.split()
        if not targets or not targets[0].endswith(".vo"):
            continue
        src = targets[0][:-1]
        if src not in fset:
            continue
        for tok in right.split():
            if tok.endswith(".vo"):
                d = tok[:-1]
                if d in fset and d != src:
                    deps[src].add(d)
    return deps


def first_error(output, path):
    """(file, line, message, c0, c1) of the first error in [output]; the
    columns are bytes from the start of the line, and may run past it."""
    m = re.search(r'File "([^"]*)", line (\d+), characters (\d+)-(\d+):\n'
                  r'(Error:(?:.*\n?){1,40})', output)
    if not m:
        return None
    msg = m.group(5).strip()
    return (m.group(1), int(m.group(2)), msg, int(m.group(3)),
            int(m.group(4)))


SEM = threading.BoundedSemaphore(int(os.environ.get("ROCQS", "40")))
INNER = cf.ThreadPoolExecutor(64)


def run_rocq(mode, path, cwd=None):
    with SEM:
        return run_rocq_now(mode, path, cwd)


def run_rocq_now(mode, path, cwd=None):
    t0 = time.time()
    try:
        p = subprocess.run(["rocq", "compile", mode] + FLAGS + [path],
                           env=ENV, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, universal_newlines=True,
                           timeout=TIMEOUT, cwd=cwd)
        return p.returncode, p.stdout + p.stderr, time.time() - t0
    except subprocess.TimeoutExpired:
        return -9, "TIMEOUT", time.time() - t0


def vos():
    files = sources()
    deps = dependencies(files)
    for f in files:
        for ext in (".vo", ".vos", ".vok", ".glob"):
            q = f[:-2] + ext
            if os.path.exists(q) and os.path.getmtime(q) < os.path.getmtime(f):
                os.remove(q)
    done = set()
    failed = {}
    lock = threading.Lock()
    pending = set(files)
    # a file whose .vos is newer than its source and its dependencies'
    def fresh(f):
        v = f[:-2] + ".vos"
        if not os.path.exists(v):
            return False
        mt = os.path.getmtime(v)
        if mt < os.path.getmtime(f):
            return False
        return all(os.path.exists(d[:-2] + ".vos")
                   and os.path.getmtime(d[:-2] + ".vos") <= mt
                   for d in deps[f])

    with cf.ThreadPoolExecutor(JOBS) as ex:
        running = {}
        while pending or running:
            for f in sorted(pending):
                if any(d in failed for d in deps[f]):
                    pending.discard(f)
                    failed[f] = ("blocked", 0, "waits for " + ", ".join(
                        os.path.basename(d) for d in deps[f] if d in failed))
                    continue
                if all(d in done for d in deps[f]):
                    pending.discard(f)
                    if fresh(f):
                        done.add(f)
                        continue
                    running[ex.submit(vos_file, f)] = f
            if not running:
                if pending:
                    continue
                break
            finished, _ = cf.wait(list(running), return_when=cf.FIRST_COMPLETED)
            for fut in finished:
                f = running.pop(fut)
                rc, out, dt = fut.result()
                if rc == 0:
                    done.add(f)
                else:
                    err = first_error(out, f)
                    failed[f] = ("error",) + (err[1:3] if err else
                                              (0, out[-600:]))
    with open(os.path.join(S, "vos.tsv"), "w") as fh:
        for f in sorted(failed):
            kind, line, msg = failed[f]
            fh.write("%s\t%s\t%d\t%s\n" % (os.path.relpath(f, R), kind, line,
                                           msg.replace("\n", " ¶ ")))
    errs = [f for f in failed if failed[f][0] == "error"]
    print("vos: %d done, %d errors, %d blocked" % (
        len(done), len(errs), len(failed) - len(errs)))
    for f in sorted(errs):
        kind, line, msg = failed[f]
        print("%s:%d: %s" % (os.path.relpath(f, R), line,
                             " ".join(msg.split())[:400]))


SUGGEST = {}
if os.path.exists(os.path.join(S, "suggest.json")):
    import json
    with open(os.path.join(S, "suggest.json")) as _fh:
        SUGGEST = json.load(_fh)


def admitted_text(path, name):
    """What stands for a proof that is not run: in a section, with the
    variables that the proof uses, so that the lemma is the same lemma
    after the section."""
    using = SUGGEST.get(os.path.relpath(path, R), {}).get(name)
    if using is None:
        b = os.path.basename(path)
        for suffix in ("__chk.v",):
            if b.endswith(suffix):
                b = b[:-len(suffix)] + ".v"
        b = re.sub(r"__one\d+\.v$", ".v", b)
        using = SUGGEST.get(os.path.relpath(
            os.path.join(os.path.dirname(path), b), R), {}).get(name)
    if using is None:
        return "Proof. Admitted."
    return using + " Admitted."


def suggest():
    """The [Proof using] of every proof of a section, asked of Rocq on
    the tree as it is (to be run on the tree before the sweep)."""
    import json
    files = [f for f in sources()
             if re.search(r"^Section\b", open(f, encoding="utf-8").read(),
                          re.M)]
    out = {}

    def one(f):
        with SEM:
            p = subprocess.run(
                ["rocq", "compile", "-vok", "-set", "Suggest Proof Using"]
                + FLAGS + [f], env=ENV, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, universal_newlines=True)
        text = p.stdout + p.stderr
        found = {}
        for m in re.finditer(
                r"The\s+proof\s+of\s+(\S+)\s+should\s+start\s+with\s+one\s+"
                r"of\s+the\s+following\s+commands:\s*"
                r"(Proof\s+using[^.]*\.)", text):
            using = " ".join(m.group(2).split())
            if re.fullmatch(r"Proof using\s*\.", using):
                using = "Proof using Type."
            found.setdefault(m.group(1), using)
        return f, p.returncode, found

    with cf.ThreadPoolExecutor(JOBS) as ex:
        for f, rc, found in ex.map(one, files):
            out[os.path.relpath(f, R)] = found
            print("%-50s rc=%d %d proofs in sections" % (
                os.path.basename(f), rc, len(found)), flush=True)
    with open(os.path.join(S, "suggest.json"), "w") as fh:
        json.dump(out, fh, indent=0, sort_keys=True)


PROOF_START = re.compile(r"^Proof\b")
PROOF_END = re.compile(r"^(Qed|Defined|Admitted|Abort)\.")
DECL = re.compile(
    r"^(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Program)\s+)*"
    r"(Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|Definition|"
    r"Fixpoint|Instance|Let)\s+([A-Za-z_][A-Za-z0-9_']*)")


def proofs_of(lines):
    """[(name, first, last)]: lines of each proof, 0-based, inclusive, from
    the line of [Proof] to the line of [Qed]."""
    out = []
    i = 0
    n = len(lines)
    name = None
    while i < n:
        m = DECL.match(lines[i])
        if m:
            name = m.group(2)
        if PROOF_START.match(lines[i]):
            j = i
            if re.search(r"\b(Qed|Defined|Admitted)\.\s*$", lines[i]):
                out.append((name, i, i))
            else:
                j = i + 1
                while j < n and not PROOF_END.match(lines[j]):
                    j += 1
                out.append((name, i, min(j, n - 1)))
            i = j + 1
            continue
        i += 1
    return out


def vos_file(path):
    """[rocq compile -vos], getting past the proofs that are run in this
    mode (those of a section) and fail: such a proof is admitted in place
    for the compilation, and the file is restored afterwards."""
    with open(path, encoding="utf-8") as fh:
        original = fh.read()
    lines = original.split("\n")
    proofs = proofs_of(lines)
    admitted = set()
    total = 0.0
    try:
        while True:
            if admitted:
                cur = list(lines)
                for idx in admitted:
                    name, a, b = proofs[idx]
                    cur[a] = admitted_text(path, name)
                    for k in range(a + 1, b + 1):
                        cur[k] = ""
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write("\n".join(cur))
            rc, out, dt = run_rocq("-vos", path)
            total += dt
            if rc == 0:
                return rc, out, total
            err = first_error(out, path)
            if not err:
                return rc, out, total
            line = err[1]
            hit = None
            for idx, (name, a, b) in enumerate(proofs):
                if a <= line - 1 <= b:
                    hit = idx
                    break
            if hit is None or hit in admitted:
                return rc, out, total
            admitted.add(hit)
    finally:
        if admitted:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(original)
            v = path[:-2] + ".vos"
            if os.path.exists(v):
                now = time.time() + 1
                os.utime(v, (now, now))


def vok_file(path):
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    proofs = proofs_of(lines)
    broken = []  # (name, line, message)
    repairs = []
    changed = False
    admitted = set()
    passed_before = 0  # proofs that end before this line have passed
    tmp = path[:-2] + "__chk.v"
    base = os.path.basename(path)[:-2]
    total = 0.0
    status = "ok"
    rounds = 0
    while True:
        rounds += 1
        cur = list(lines)
        for idx, (name, a, b) in enumerate(proofs):
            if idx in admitted or b < passed_before:
                cur[a] = admitted_text(path, name)
                for k in range(a + 1, b + 1):
                    cur[k] = ""
        with open(tmp, "w", encoding="utf-8") as fh:
            fh.write(re.sub(r"(?<![\w'.])%s\." % base, base + "__chk.",
                            "\n".join(cur)))
        rc, out, dt = run_rocq("-vok", tmp)
        total += dt
        if rc == 0:
            break
        if rc == -9:
            status = "timeout"
            broken.append(("?", passed_before, "TIMEOUT after line %d"
                           % passed_before))
            break
        err = first_error(out, tmp)
        if not err:
            status = "unparsed"
            broken.append(("?", 0, out[-800:]))
            break
        _, line, msg, c0, c1 = err
        hit = None
        for idx, (name, a, b) in enumerate(proofs):
            if a <= line - 1 <= b:
                hit = idx
                break
        if hit is not None and hit not in admitted and REPAIR:
            fixed, lines, log, err2 = repair_proof(path, lines, proofs, hit,
                                                   (line, c0, c1, msg))
            total += sum(x[-1] for x in log if x[0] == "time")
            log = [x for x in log if x[0] != "time"]
            repairs.extend((proofs[hit][0],) + x for x in log)
            if fixed:
                changed = True
                continue
            if log:
                changed = True
            line, c0, c1, msg = err2
        if hit is None or hit in admitted:
            status = "statement"
            broken.append(("(not in a proof)", line, msg))
            break
        admitted.add(hit)
        broken.append((proofs[hit][0], line, msg))
        passed_before = proofs[hit][1]
    for ext in (".v", ".vok", ".vos", ".glob", ".vo"):
        q = tmp[:-2] + ext
        if os.path.exists(q):
            os.remove(q)
    aux = os.path.join(os.path.dirname(tmp),
                       "." + os.path.basename(tmp)[:-2] + ".aux")
    if os.path.exists(aux):
        os.remove(aux)
    if changed:
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))
    return path, status, len(proofs), broken, total, rounds, repairs


# ---- repairs driven by the errors ---------------------------------------

HP = "hp"
REPAIR = False
ATOM = re.compile(r"\[|\(|[A-Za-z_][A-Za-z0-9_']*|\?[A-Za-z_]*|_|->|<-|\*")


def char_offset(text, lines, line, col):
    """The offset in [text] of byte [col] of line [line] (1-based)."""
    start = sum(len(l) + 1 for l in lines[:line - 1])
    rest = "\n".join(lines[line - 1:]).encode("utf-8")
    return start + len(rest[:col].decode("utf-8", errors="ignore"))


def close_of(text, i):
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = [pairs[text[i]]]
    j = i + 1
    while j < len(text) and stack:
        c = text[j]
        if c in pairs:
            stack.append(pairs[c])
        elif c in ")]}":
            if c != stack[-1]:
                return None
            stack.pop()
        j += 1
    return j - 1 if not stack else None


def intros_atoms(text, pos, limit):
    """Positions after each pattern of the [intros] whose keyword ends at
    [pos]: [(end, pattern text)]."""
    out = []
    i = pos
    while i < limit:
        while i < limit and text[i] in " \n\t":
            i += 1
        m = ATOM.match(text, i)
        if not m or i >= limit:
            break
        if m.group(0) in "[(":
            j = close_of(text, i)
            if j is None:
                break
            out.append((j + 1, text[i:j + 1]))
            i = j + 1
        else:
            if m.group(0) in ("in", "until", "at"):
                break
            out.append((m.end(), m.group(0)))
            i = m.end()
    return out


def candidates(text, a, b, e0, e1, msg):
    """Edits to try, best first: [(rule, [(start, end, replacement)])].
    [a, b) is the proof, [e0, e1) where the error is."""
    out = []
    span = text[e0:e1]
    if 'Cannot infer this placeholder of type "heap"' in msg and span == "_":
        out.append(("placeholder", [(e0, e1, HP)]))
    if re.search(r'expected to have type\s+"heap"', msg):
        out.append(("argument", [(e0, e0, HP + " ")]))
        out.append(("argument", [(e0, e0, "_ ")]))
    if re.search(r'has type\s+"∀ hp : heap,', msg):
        out.append(("applied to the heap", [(e1, e1, " " + HP)]))
        out.append(("applied to the heap _", [(e1, e1, " _")]))
    if msg.startswith(("Error: Expects a disjunctive pattern",
                       "Error: Expects a conjunctive pattern",
                       "Error: Not a primitive equality")):
        out.append(("pattern", [(e0, e0, HP + " ")]))
    if "Unable to find an instance for the variable hp" in msg:
        for m in reversed(list(re.finditer(
                r"(?:statics|extended)[\w']*(?=\s*\))", span))):
            out.append(("last argument", [(e0 + m.end(), e0 + m.end(),
                                           " " + HP)]))
            out.append(("last argument _", [(e0 + m.end(), e0 + m.end(),
                                             " _")]))
    # the patterns that take apart the comparison of two exits
    ls = text.rfind("\n", 0, e0) + 1
    le = text.find("\n", max(e1, e0))
    le = len(text) if le == -1 else le
    for pat, rep in [("[-> ->]", "[-> [-> ->]]"), ("[<- <-]", "[<- [<- <-]]"),
                     ("[= <- <-]", "[= <- <- <-]"),
                     ("[= -> ->]", "[= -> -> ->]"),
                     ("[= <- ->]", "[= <- -> ->]")]:
        i = text.find(pat, ls, le)
        while i != -1:
            out.append(("exits compared", [(i, i + len(pat), rep)]))
            i = text.find(pat, i + 1, le)
    # a pattern of four names that takes a state apart
    if "hp was not found" in msg:
        for m in reversed(list(re.finditer(
                r"\[([A-Za-z_][\w']*(?:\s+[A-Za-z_][\w']*){3})\]",
                text[a:e0]))):
            out.append(("state pattern", [(a + m.end() - 1, a + m.end() - 1,
                                           " " + HP)]))
    # the heap named where it is not in scope
    if span == HP and "hp was not found" in msg:
        out.append(("heap as _", [(e0, e1, "_")]))
    # an explicit application whose arguments are one short before here;
    # tried after the names of the [intros]
    generic = []

    def is_argument(pos):
        k = pos
        while k > a and text[k - 1] in " \n\t":
            k -= 1
        return k > a and (text[k - 1].isalnum() or text[k - 1] in "_')]")

    if re.search(r"has type[\s\S]*while it is expected to have type", msg):
        j = e0
        starts = []
        for _ in range(5):
            k = j
            while k > a and text[k - 1] in " \n\t":
                k -= 1
            if k <= a:
                break
            if text[k - 1] in ")]":
                depth = 0
                m = k - 1
                while m > a:
                    if text[m] in ")]":
                        depth += 1
                    elif text[m] in "([":
                        depth -= 1
                        if depth == 0:
                            break
                    m -= 1
                start = m
            else:
                m = k
                while m > a and (text[m - 1].isalnum()
                                 or text[m - 1] in "_'.?@"):
                    m -= 1
                start = m
            if start == k or not is_argument(start):
                break
            starts.append(start)
            j = start
        if is_argument(e0):
            generic.append(("argument _", [(e0, e0, "_ ")]))
        for st in starts:
            generic.append(("argument before _", [(st, st, "_ ")]))
    # the name in a pattern that takes a relation on states apart
    for m in reversed(list(re.finditer(
            r"(?<![\w'])(?:statics|extended)[\w']*", text[a:e0]))[-12:]):
        end = a + m.end()
        # inside an [as [...]] pattern: the nearest bracket before is open
        seg = text[a:end]
        if seg.count("[") <= seg.count("]"):
            continue
        if text[end:end + 1 + len(HP)] == " " + HP:
            continue
        opening = text.rfind("[", a, end)
        closing = text.rfind("]", a, end)
        if opening < closing:
            continue
        out.append(("as pattern", [(end, end, " " + HP)]))
    # the name in an [intros]
    found = [m for m in re.finditer(r"(?<![\w'])intros\b", text[a:max(e1, e0)])]
    for m in reversed(found[-4:]):
        kw_end = a + m.end()
        atoms = intros_atoms(text, kw_end, b)
        ends = [end for end, _ in atoms]
        first, second, third = [], [], []
        for end, pat in atoms:
            if re.match(r"(statics|extended)", pat):
                first.append(end)
            elif re.match(r"(exit_)?vs\d*'*$", pat):
                second.append(end)
            else:
                third.append(end)
        order = list(reversed(first)) + list(reversed(second))
        if ends and ends[-1] not in order:
            order.append(ends[-1])
        order += [e for e in reversed(third) if e not in order]
        order.append(kw_end)
        for end in order[:9]:
            if text[end:end + 1 + len(HP)] == " " + HP and not \
                    text[end + 1 + len(HP):end + 2 + len(HP)].isalnum():
                continue
            out.append(("intros", [(end, end, " " + HP)]))
    out += generic
    # where the name is taken already, another name
    for rule, edits in list(out):
        if rule in ("intros", "pattern", "as pattern"):
            out.append((rule + " (another name)",
                        [(st, en, rep.replace(HP, HP + "'"))
                         for st, en, rep in edits]))
    # ---- several edits at once ------------------------------------------
    singles = [x for x in out if "another name" not in x[0]]
    intros_edits = [e for rule, e in singles if rule == "intros"][:3]
    # the sentence of the error
    ss = max(text.rfind(". ", a, e0), text.rfind(".\n", a, e0),
             text.rfind("- ", a, e0), text.rfind("+ ", a, e0),
             text.rfind("* ", a, e0))
    ss = a if ss == -1 else ss + 2
    se_candidates = [x for x in (text.find(". ", max(e0, e1 - 1)),
                                 text.find(".\n", max(e0, e1 - 1))) if x != -1]
    se = min(se_candidates) if se_candidates else b
    sent = text[ss:se]
    compound = []
    # every comparison of exits on the line
    edits = []
    for pat, rep in [("[-> ->]", "[-> [-> ->]]"), ("[<- <-]", "[<- [<- <-]]"),
                     ("[= <- <-]", "[= <- <- <-]"),
                     ("[= -> ->]", "[= -> -> ->]")]:
        i = text.find(pat, ss, se)
        while i != -1:
            edits.append((i, i + len(pat), rep))
            i = text.find(pat, i + 1, se)
    if len(edits) > 1:
        compound.append(("exits compared", edits))
    # the heap after every static environment given as an argument
    for fill in (HP, "_"):
        edits = []
        for m in re.finditer(r"(?<![\w'])(?:statics|extended)[\w']*(?=[\s)])",
                             sent):
            pos = ss + m.end()
            before = sent[:m.start()]
            if before.count("(") <= before.count(")"):
                continue
            if re.match(r"\s+(?:%s|_)(?![\w'])" % HP, text[pos:pos + 6]):
                continue
            edits.append((pos, pos, " " + fill))
        if edits:
            compound.append(("heap after statics", edits))
            for ie in intros_edits:
                if not any(st <= ie[0][0] <= en for st, en, _ in edits):
                    compound.append(("heap after statics, intros",
                                     edits + ie))
    # one more placeholder in every application to placeholders
    edits = []
    for m in re.finditer(r"[A-Za-z_][\w']*((?:\s+_){3,})(?![\w'])", sent):
        edits.append((ss + m.end(1), ss + m.end(1), " _"))
    if edits:
        compound.append(("one more placeholder", edits))
        for ie in intros_edits:
            compound.append(("one more placeholder, intros", edits + ie))
    # an intros with each of the first other edits
    others = [(rule, e) for rule, e in singles if rule != "intros"][:4]
    for ie in intros_edits[:2]:
        for rule, e in others:
            if not any(st <= ie[0][0] <= en for st, en, _ in e):
                compound.append((rule + ", intros", e + ie))
    return out[:22] + compound[:14]


def apply_edits(text, edits):
    for start, end, rep in sorted(edits, reverse=True):
        text = text[:start] + rep + text[end:]
    return text


COUNTER = [0]
COUNTER_LOCK = threading.Lock()


def check_single(path, text, proofs, idx):
    """Check proof [idx] alone: None, or (line, c0, c1, msg), or "other"."""
    lines = text.split("\n")
    cur = list(lines)
    for k, (name, a, b) in enumerate(proofs):
        if k != idx:
            cur[a] = admitted_text(path, name)
            for j in range(a + 1, b + 1):
                cur[j] = ""
    base = os.path.basename(path)[:-2]
    with COUNTER_LOCK:
        COUNTER[0] += 1
        serial = COUNTER[0]
    tmp = path[:-2] + "__one%d.v" % serial
    tbase = os.path.basename(tmp)[:-2]
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(re.sub(r"(?<![\w'.])%s\." % base, tbase + ".",
                        "\n".join(cur)))
    rc, out, dt = run_rocq("-vok", tmp)
    for ext in (".v", ".vok", ".vos", ".glob", ".vo"):
        q = tmp[:-2] + ext
        if os.path.exists(q):
            os.remove(q)
    aux = os.path.join(os.path.dirname(tmp), "." + tbase + ".aux")
    if os.path.exists(aux):
        os.remove(aux)
    if rc == 0:
        return None, dt
    err = first_error(out, tmp)
    if not err:
        return "other", dt
    _, line, msg, c0, c1 = err
    name, a, b = proofs[idx]
    if not (a <= line - 1 <= b):
        return "other", dt
    return (line, c0, c1, msg), dt


def repair_proof(path, lines, proofs, idx, err):
    """Try the repairs on proof [idx], whose first error is [err].
    Returns (fixed, lines, log, last error)."""
    text = "\n".join(lines)
    log = []
    spent = 0.0
    name, pa, pb = proofs[idx]
    for _round in range(14):
        line, c0, c1, msg = err
        cur_lines = text.split("\n")
        a = sum(len(l) + 1 for l in cur_lines[:pa])
        b = sum(len(l) + 1 for l in cur_lines[:pb + 1])
        e0 = char_offset(text, cur_lines, line, c0)
        e1 = char_offset(text, cur_lines, line, c1)
        progressed = False
        cands = []
        seen = set()
        for rule, edits in candidates(text, a, b, e0, e1, msg):
            key = tuple(edits)
            if key in seen:
                continue
            seen.add(key)
            cands.append((rule, edits))
        cands = cands[:36]
        for batch_start in range(0, len(cands), 8):
            batch = cands[batch_start:batch_start + 8]
            futs = [INNER.submit(check_single, path, apply_edits(text, edits),
                                 proofs, idx) for _, edits in batch]
            results = [f.result() for f in futs]
            spent += sum(dt for _, dt in results)
            for (rule, edits), (res, dt) in zip(batch, results):
                if res == "other":
                    continue
                if res is not None:
                    m2 = res[3]
                    if "Syntax error" in m2 or "already used" in m2:
                        continue
                    if "hp was not found" in m2 and \
                            "hp was not found" not in msg:
                        continue
                    before = sum(len(rep) - (end - start)
                                 for start, end, rep in edits
                                 if start <= e0
                                 and text.count("\n", start, e0) == 0)
                    later = res[0] > line or (
                        res[0] == line and res[1] > c0 + max(before, 0))
                    if not later:
                        continue
                first = min(start for start, _, _ in edits)
                ln = text.count("\n", 0, first) + 1
                log.append((rule, ln, cur_lines[ln - 1].strip()[:100]))
                text = apply_edits(text, edits)
                progressed = True
                if res is None:
                    log.append(("time", spent))
                    return True, text.split("\n"), log, None
                err = res
                break
            if progressed:
                break
        if not progressed:
            break
    log.append(("time", spent))
    return False, text.split("\n"), log, err


def vok(args):
    global REPAIR
    if args and args[0] == "--repair":
        REPAIR = True
        args = args[1:]
    files = sources()
    if args:
        files = [f for f in files
                 if any(os.path.basename(f) == a or f.endswith(a)
                        for a in args)]
    results = []
    all_repairs = []
    with cf.ThreadPoolExecutor(JOBS) as ex:
        futs = [ex.submit(vok_file, f) for f in files]
        for fut in cf.as_completed(futs):
            path, status, n, broken, total, rounds, repairs = fut.result()
            results.append((path, status, n, broken, total, rounds))
            all_repairs.extend((path,) + r for r in repairs)
            print("%-52s %-9s %4d proofs %3d broken %3d repairs %6.0fs" % (
                os.path.basename(path), status, n, len(broken),
                len(repairs), total), flush=True)
    out = os.path.join(S, "broken.tsv" if not args else "broken-part.tsv")
    with open(out, "w") as fh:
        for path, status, n, broken, total, rounds in sorted(results):
            for name, line, msg in broken:
                fh.write("%s\t%s\t%s\t%d\t%s\n" % (
                    os.path.relpath(path, R), status, name, line,
                    msg.replace("\n", " ¶ ")))
    with open(os.path.join(S, "files.tsv" if not args else
                           "files-part.tsv"), "w") as fh:
        for path, status, n, broken, total, rounds in sorted(results):
            fh.write("%s\t%s\t%d\t%d\t%.0f\n" % (
                os.path.relpath(path, R), status, n, len(broken), total))
    if REPAIR:
        with open(os.path.join(S, "repairs.tsv" if not args else
                               "repairs-part.tsv"), "a") as fh:
            for path, name, rule, ln, old in sorted(all_repairs):
                fh.write("%s\t%s\t%s\t%d\t%s\n" % (
                    os.path.relpath(path, R), name, rule, ln, old))
        print("repairs: %d in %d proofs" % (
            len(all_repairs),
            len({(r[0], r[1]) for r in all_repairs})))
    print("files: %d; with a broken proof: %d; broken proofs: %d" % (
        len(results), sum(1 for r in results if r[3]),
        sum(len(r[3]) for r in results)))


if __name__ == "__main__":
    if sys.argv[1] == "vos":
        vos()
    elif sys.argv[1] == "suggest":
        suggest()
    else:
        vok(sys.argv[2:])
