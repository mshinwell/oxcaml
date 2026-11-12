#!/usr/bin/env python3
"""The sweep that puts the heap into [state]: the edits that need no
compilation.

Usage, from the root of a clean checkout:

    python3 middle_end/flambda2/rocq/requests/C4-heap-sweep.py . \\
        [--report FILE]

It edits the .v files of middle_end/flambda2/rocq and
middle_end/flambda2/types/rocq in place:

  1. FlambdaSemanticsSpec.v: the field [state_heap], last in [state];
     the heap last in [Exit] and in [Exits] (and in [Stack_exit] of
     FlambdaTrapSpec.v).
  2. Every application of [State], [Exit], [Exits], [Stack_exit] and of
     the functions that build a state (TARGETS and EXTRA below) gains
     the heap as its last argument: [hp]; [_] in a pattern whose branch
     does not use it; [(state_heap s)] beside [(state_statics s)];
     [empty_heap] beside [empty_static_env] and in a state or an exit
     that an example writes out.
  3. A statement that now mentions the heap gains a binder for it, after
     the binder of the static environment beside which it is first used
     (or of the values of an exit, where there is no static
     environment). A section whose variable is that static environment
     gains a variable (in a sentence that declares several groups of
     variables, after the group of the static environment).
  4. Where the binder went into the leading quantifier of a statement,
     the first [intros] of its proof gains the name at the same
     position.
  5. An explicit application, in a proof, of a lemma that gained a
     binder gains [_] at the position of the binder.
  6. In a proof that builds a state from the parts of one it took apart
     with a pattern of four names, the pattern gains the name.
  7. Where two results are matched together and the values of their
     exits are compared, their heaps are compared.
  8. A quantifier inside a statement that binds a static environment,
     under a statement that has the heap already, binds a heap of its
     own, [hp'].
  9. In a branch of a match on an exit that is compared with a state or
     an application at the heap of the statement, the exit matched has
     its own heap, [hp'], and the other side keeps [hp].
 10. A definition that builds a state from its arguments gains the heap
     as an argument, and so does one that calls it: the first phase is
     run again until no such definition is new.

It does not wrap the lines it makes longer than 80 columns. What it
cannot place it reports (UNBOUND, PROOF-NO-HEAP, INTROS-LATE, and
APPLICATION-OUTSIDE for an application, outside its section, of a
lemma of a section that gained the variable): the second script,
C4-heap-sweep-check.py, compiles the tree and repairs what the error
messages show.

requests/C4-heap-fallout.md, "The heap in [state]: the rehearsals of
the sweep", says what this did on 106a2d501a.
"""
import json
import os
import re
import sys

HP = "hp"
HEAP_TYPE = "heap"

KEYWORDS = {
    "in", "with", "as", "end", "then", "else", "by", "at", "using", "eqn",
    "return", "match", "if", "let", "fun", "forall", "exists", "struct",
    "for", "of", "into",
}

# name -> number of explicit arguments before the heap
EXIT_LIKE = {"Exit", "Exits", "Stack_exit"}
TARGETS = {
    "State": 4,
    "Exit": 2,
    "Exits": 2,
    "Stack_exit": 2,
    "apply_cont_value": 3,
    "apply_continuation": 4,
    "call_function": 8,
}

# Definitions that gain the heap as an argument because their body builds
# a state or calls one that does: name -> number of explicit arguments
# before it. The script reports a definition that gains the argument and
# is not here (DEF-ARG): add it and run again from a clean tree.
EXTRA = {
    "call_code": 8,
    "run_call": 6,
    "unwind": 4,
    "stack_enter": 3,
    "stack_call": 4,
    "stack_run_call": 6,
    "stack_apply_cont": 4,
}

DECL_KW = (
    "Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|Definition|"
    "Fixpoint|CoFixpoint|Inductive|CoInductive|Variant|Record|Variable|"
    "Variables|Hypothesis|Hypotheses|Context|Let|Instance|Axiom|Parameter"
)
LEMMA_KW = {"Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition"}
OTHER_KW = (
    "Ltac|Notation|Section|End|Module|Require|From|Import|Export|Open|"
    "Close|Set|Unset|Arguments|Opaque|Transparent|Hint|Create|Scheme|"
    "Extraction|Extract|Check|Print|Compute|Eval|Goal|Proof|Qed|Defined|"
    "Admitted|Abort|Obligation|Next|Solve|Tactic|Declare|Existing|"
    "Coercion|Canonical|Add|Infix|Reserved|Implicit|Generalizable|"
    "Local|Global|Program|Derive|Strategy|Typeclasses|Unshelve|Fail|Time|"
    "Search|About|Locate|Recursive|Separate|Cd|Redirect"
)
UNIT_RE = re.compile(
    r"^(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Program|Polymorphic)\s+)*"
    r"(" + DECL_KW + "|" + OTHER_KW + r")\b",
    re.M,
)
IDENT_RE = re.compile(
    r"@?[A-Za-z_\u00C0-\u024F][A-Za-z0-9_'\u00C0-\u024F]*"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
NUM_RE = re.compile(r"\d+")
SCOPE_RE = re.compile(r"%[A-Za-z_]\w*")


def mask_comments(text):
    n = len(text)
    mask = bytearray(n)
    i = 0
    depth = 0
    while i < n:
        if depth == 0 and text[i] == '"':
            j = text.find('"', i + 1)
            while j != -1 and text.startswith('""', j):
                j = text.find('"', j + 2)
            if j == -1:
                j = n - 1
            for t in range(i, j + 1):
                mask[t] = 2
            i = j + 1
            continue
        if text.startswith("(*", i):
            depth += 1
            mask[i] = 1
            mask[i + 1] = 1
            i += 2
            continue
        if depth > 0 and text.startswith("*)", i):
            mask[i] = 1
            mask[i + 1] = 1
            depth -= 1
            i += 2
            continue
        if depth > 0:
            mask[i] = 1
        i += 1
    return mask


class Doc:
    def __init__(self, path, text):
        self.path = path
        self.text = text
        self.mask = mask_comments(text)
        self.inserts = []  # (pos, string, order)
        self.replaces = []  # (start, end, string)

    def skip_ws(self, i):
        t, m = self.text, self.mask
        n = len(t)
        while i < n and (t[i].isspace() or m[i] == 1):
            i += 1
        return i

    def match_close(self, i):
        t, m = self.text, self.mask
        pairs = {"(": ")", "[": "]", "{": "}"}
        stack = [pairs[t[i]]]
        j = i + 1
        n = len(t)
        while j < n and stack:
            if m[j]:
                j += 1
                continue
            c = t[j]
            if c in pairs:
                stack.append(pairs[c])
            elif c in ")]}":
                if c != stack[-1]:
                    return None
                stack.pop()
            j += 1
        if stack:
            return None
        return j - 1

    def read_atom(self, i):
        t = self.text
        i = self.skip_ws(i)
        if i >= len(t):
            return None
        ch = t[i]
        if ch in "([{":
            j = self.match_close(i)
            if j is None:
                return None
            j += 1
            m = SCOPE_RE.match(t, j)
            if m:
                j = m.end()
            return (i, j)
        if ch == '"':
            j = i
            while j < len(t) and self.mask[j] == 2:
                j += 1
            return (i, j)
        if ch == "?":
            m = IDENT_RE.match(t, i + 1)
            return (i, m.end()) if m else (i, i + 1)
        m = IDENT_RE.match(t, i)
        if m:
            if m.group(0) in KEYWORDS:
                return None
            return (i, m.end())
        m = NUM_RE.match(t, i)
        if m:
            j = m.end()
            m2 = SCOPE_RE.match(t, j)
            if m2:
                j = m2.end()
            return (i, j)
        return None

    def read_atoms(self, i, limit):
        atoms = []
        while len(atoms) < limit:
            a = self.read_atom(i)
            if a is None:
                break
            atoms.append(a)
            i = a[1]
        return atoms

    def insert(self, pos, s, order=0):
        self.inserts.append((pos, order, s))

    def result(self):
        t = self.text
        ops = [(p, o, s) for (p, o, s) in self.inserts]
        ops.sort(key=lambda x: (x[0], x[1]))
        out = []
        last = 0
        for p, _, s in ops:
            out.append(t[last:p])
            out.append(s)
            last = p
        out.append(t[last:])
        return "".join(out)


def find_units(doc):
    """[(start, end, keyword)] of the commands that start in column 0."""
    starts = []
    for m in UNIT_RE.finditer(doc.text):
        if doc.mask[m.start()]:
            continue
        starts.append((m.start(), m.group(1)))
    units = []
    for idx, (s, kw) in enumerate(starts):
        e = starts[idx + 1][0] if idx + 1 < len(starts) else len(doc.text)
        units.append((s, e, kw))
    return units


def paren_stack(doc, start, pos):
    """Positions of the brackets open at [pos], from [start]."""
    t, m = doc.text, doc.mask
    stack = []
    for j in range(start, pos):
        if m[j]:
            continue
        c = t[j]
        if c in "([{":
            stack.append(j)
        elif c in ")]}":
            if stack:
                stack.pop()
    return tuple(stack)


BINDER_PAREN_RE = re.compile(
    r"([({])\s*((?:[A-Za-z_][A-Za-z0-9_']*\s+)*[A-Za-z_][A-Za-z0-9_']*)"
    r"\s*:(?!=)"
)
BINDER_BARE_TYPED_RE = re.compile(
    r"(∀|∃|forall|exists|fun|λ)\s+"
    r"((?:[A-Za-z_][A-Za-z0-9_']*\s+)*[A-Za-z_][A-Za-z0-9_']*)\s*:(?!=)"
)
BINDER_BARE_UNTYPED_RE = re.compile(
    r"(∀|∃|forall|exists|fun|λ)\s+"
    r"((?:[A-Za-z_][A-Za-z0-9_']*\s+)*[A-Za-z_][A-Za-z0-9_']*)\s*(,|=>)"
)


def binders_in(doc, start, end):
    """Binder groups in [start, end): dicts with kind, names, pos, ins."""
    t = doc.text
    out = []
    for m in BINDER_PAREN_RE.finditer(t, start, end):
        if doc.mask[m.start()]:
            continue
        close = doc.match_close(m.start())
        if close is None or close >= end:
            continue
        # a binder group, not a cast: what precedes is a binder context.
        # Casts [(x : T)] in terms are rare; accept.
        out.append({
            "kind": "paren" if m.group(1) == "(" else "brace",
            "names": m.group(2).split(),
            "pos": m.start(),
            "close": close,
        })
    for m in BINDER_BARE_TYPED_RE.finditer(t, start, end):
        if doc.mask[m.start()]:
            continue
        # the type runs to the next [,] or [=>] at the same depth
        j = m.end()
        depth = 0
        stop = None
        while j < end:
            if doc.mask[j]:
                j += 1
                continue
            c = t[j]
            if c in "([{":
                depth += 1
            elif c in ")]}":
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and (c == "," or t.startswith("=>", j)):
                stop = j
                break
            j += 1
        if stop is None:
            continue
        out.append({
            "kind": "bare_typed",
            "names": m.group(2).split(),
            "pos": m.start(),
            "names_start": m.start(2),
            "stop": stop,
            "quant_end": m.end(1),
        })
    for m in BINDER_BARE_UNTYPED_RE.finditer(t, start, end):
        if doc.mask[m.start()]:
            continue
        out.append({
            "kind": "bare_untyped",
            "names": m.group(2).split(),
            "pos": m.start(),
            "names_start": m.start(2),
            "names_end": m.end(2),
        })
    out.sort(key=lambda b: b["pos"])
    return out


def parse_header(doc, start, end, kw):
    """Of a declaration: its name, the explicit names of its header
    binders with the position of each group, and the names of the leading
    quantifier of its statement, with the groups."""
    t = doc.text
    m = re.compile(
        r"(?:#\[[^\]]*\]\s*)?(?:(?:Local|Global|Program)\s+)*" + kw + r"\s+"
        r"([A-Za-z_][A-Za-z0-9_']*)"
    ).match(t, start)
    if not m:
        return None
    name = m.group(1)
    i = m.end()
    header = []  # (group_pos, names, explicit)
    while True:
        i = doc.skip_ws(i)
        if i < end and t[i] in "({":
            close = doc.match_close(i)
            if close is None:
                break
            inner = t[i + 1:close]
            if ":" in inner:
                names = inner.split(":", 1)[0].split()
            else:
                names = inner.split()
            header.append((i, names, t[i] == "("))
            i = close + 1
        else:
            break
    i = doc.skip_ws(i)
    colon = None
    if i < end and t[i] == ":" and not t.startswith(":=", i):
        colon = i
    # where the statement starts: after [:] for a lemma; after [:=] for a
    # definition of a statement
    stmt_start = None
    if kw in LEMMA_KW and colon is not None:
        stmt_start = colon + 1
    elif kw == "Definition":
        j = t.find(":=", i, end)
        if j != -1:
            stmt_start = j + 2
    leading = []  # (group_pos, names)
    if stmt_start is not None:
        j = doc.skip_ws(stmt_start)
        mq = re.compile(r"(∀|forall)\s*").match(t, j)
        if mq:
            j = mq.end()
            while True:
                j = doc.skip_ws(j)
                if j < end and t[j] in "({":
                    close = doc.match_close(j)
                    if close is None:
                        break
                    inner = t[j + 1:close]
                    names = inner.split(":", 1)[0].split()
                    leading.append((j, names))
                    j = close + 1
                    continue
                mn = NAME_RE.match(t, j)
                if mn and mn.group(0) not in KEYWORDS:
                    leading.append((j, [mn.group(0)]))
                    j = mn.end()
                    k = doc.skip_ws(j)
                    if k < end and t[k] == ":":
                        # [∀ a b : T,]: one bare typed group; the names
                        # read so far are it
                        break
                    continue
                break
    return {"name": name, "header": header, "leading": leading}


TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*|\|\||[()\[\]{}|]")


def branch_end(doc, pos):
    """The end of the branch of a [match] that starts at [pos]."""
    t, m = doc.text, doc.mask
    depth = 0
    parens = 0
    for mm in TOKEN_RE.finditer(t, pos):
        if m[mm.start()]:
            continue
        tok = mm.group(0)
        if tok == "match":
            depth += 1
        elif tok == "end":
            if depth == 0:
                return mm.start()
            depth -= 1
        elif tok in "([{":
            parens += 1
        elif tok in ")]}":
            if parens == 0:
                return mm.start()
            parens -= 1
        elif tok == "|" and depth == 0 and parens == 0:
            return mm.start()
    return len(t)


class Report:
    def __init__(self):
        self.rows = []

    def add(self, path, pos_line, cls, detail):
        self.rows.append((path, pos_line, cls, detail))


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def target_regex(names):
    alt = "|".join(sorted((re.escape(n) for n in names), key=len,
                          reverse=True))
    return re.compile(r"(?<![\w'.])(" + alt + r")(?![\w'])")


def in_name_list(t, pos):
    """Whether [pos] is in a list of names given to [cbn] and the like."""
    lo = max(0, pos - 300)
    i = t.rfind("[", lo, pos)
    if i == -1 or "]" in t[i:pos]:
        return False
    head = t[max(0, i - 12):i].rstrip()
    return head.endswith(("cbn", "simpl", "cbv", "lazy", "delta", "unfold",
                          "autounfold", "compute"))


def anchor_of(doc, atom):
    """The names in an argument: the argument if it is a name, or the
    names inside it, last first."""
    s = doc.text[atom[0]:atom[1]]
    if NAME_RE.fullmatch(s):
        return [s]
    names = [n for n in NAME_RE.findall(s) if n not in KEYWORDS]
    names.reverse()
    return names or None


def process_file(path, rel, tables, report, phase):
    """phase 1: constructors and binders, intros; collects tables.
    phase 2: explicit applications of lemmas that gained a binder."""
    with open(path, encoding="utf-8") as f:
        text = f.read()
    doc = Doc(path, text)
    t = text
    base = os.path.basename(path)
    if phase == 2:
        return phase2(doc, rel, tables, report)

    targets = dict(TARGETS)
    targets.update(EXTRA)
    units = find_units(doc)

    sections = []
    for sm in re.finditer(r"^Section\s+([A-Za-z_][\w']*)\s*\.", t, re.M):
        em = re.search(r"^End\s+%s\s*\." % re.escape(sm.group(1)),
                       t[sm.end():], re.M)
        if em:
            sections.append((sm.start(), sm.end() + em.start()))

    def note_home(name, pos):
        """A lemma of a section takes the variables of the section first
        once the section is closed: its applications outside are left to
        the rules."""
        for (s0, s1) in sections:
            if s0 <= pos < s1:
                tables["lemma_home"][name] = (rel, s0, s1)

    def unit_at(pos):
        lo, hi = 0, len(units) - 1
        while lo <= hi:
            mid = (lo + hi) // 2
            s, e, _ = units[mid]
            if pos < s:
                hi = mid - 1
            elif pos >= e:
                lo = mid + 1
            else:
                return mid
        return None

    # --- the definitions ------------------------------------------------
    if base == "FlambdaSemanticsSpec.v":
        anchor_text = "  state_statics : static_env"
        p = t.find(anchor_text + "\n}.")
        if p == -1:
            report.add(rel, 0, "MISSING-DEFINITION", anchor_text.strip())
        else:
            doc.insert(p + len(anchor_text), ";\n  state_heap : heap", 0)
    for mm in re.compile(
            r"^\s*\| (?:Exit|Exits|Stack_exit) \(k : continuation\) "
            r"\(vs : list value\)$", re.M).finditer(t):
        doc.insert(mm.end(), " (%s : heap)" % HP, 0)
        report.add(rel, line_of(t, mm.start()), "CONSTRUCTOR", "")

    # --- uses of the constructors and functions ------------------------
    uses = []  # dicts: pos (insertion), unit, anchor, pattern, name
    decl_re = re.compile(r"(?:" + DECL_KW + r"|Fixpoint)\s+$")
    for m in target_regex(targets).finditer(t):
        if doc.mask[m.start()]:
            continue
        name = m.group(1)
        # the declaration of the name itself
        if decl_re.search(t[max(0, m.start() - 40):m.start()]):
            continue
        if in_name_list(t, m.start()):
            continue
        # [| Exit (k : continuation) ...]: the constructor's declaration
        n_args = targets[name]
        atoms = doc.read_atoms(m.end(), n_args)
        if len(atoms) < n_args:
            if name == "State" and t.startswith(":= State {", m.start() - 3):
                continue
            if name in ("State", "Exit", "Exits") and len(atoms) > 0:
                report.add(rel, line_of(t, m.start()), "PARTIAL",
                           "%s with %d arguments" % (name, len(atoms)))
            continue
        if name in EXIT_LIKE:
            # the declaration of the constructor has binders as atoms
            a0 = t[atoms[0][0]:atoms[0][1]]
            if a0.startswith("(k :"):
                continue
        last = atoms[-1]
        last_s = t[last[0]:last[1]]
        after = doc.skip_ws(last[1])
        u = unit_at(m.start())
        ukw = units[u][2] if u is not None else None
        line_start = t.rfind("\n", 0, m.start()) + 1
        line_head = t[line_start:m.start()]
        starts_bar = line_head.lstrip().startswith("|") and not \
            line_head.lstrip().startswith("||")
        is_pattern = t.startswith("=>", after) or (
            name in ("State",) + tuple(EXIT_LIKE) and starts_bar
            and "=>" not in line_head and ":" not in line_head
            and ukw not in ("Inductive", "CoInductive", "Variant", "Record"))
        use = {"pos": last[1], "unit": u, "name": name, "start": m.start(),
               "last": last, "args": [t[a[0]:a[1]] for a in atoms],
               "pattern": is_pattern, "anchor": None, "text": None,
               "after": after}
        arg_texts = [t[a[0]:a[1]] for a in atoms]
        if name == "State" or name in ("apply_cont_value",
                                       "apply_continuation",
                                       "call_function") or name in EXTRA:
            mproj = re.search(r"\b(state|hs)_statics\s+([A-Za-z_][\w']*)",
                              last_s)
            if last_s == "_":
                use["text"] = " _"
            elif last_s == "empty_static_env":
                use["text"] = " empty_heap"
            elif mproj:
                use["text"] = " (%s_heap %s)" % (mproj.group(1),
                                                  mproj.group(2))
            else:
                use["text"] = " " + HP
                use["anchor"] = ("statics", anchor_of(doc, last))
        else:  # Exit, Exits
            if is_pattern and "_" in arg_texts:
                use["text"] = " _"
            else:
                use["text"] = " " + HP
                use["anchor"] = ("vs", [last_s] if NAME_RE.fullmatch(last_s)
                                 else None)
        uses.append(use)

    # patterns: the heap is named where the branch uses it
    term_uses = [u for u in uses if not u["pattern"] and u["text"] == " " + HP]
    for u in uses:
        if not u["pattern"]:
            continue
        if u["text"] != " " + HP:
            continue
        u["branch_end"] = branch_end(doc, u["after"])
        inside = [v for v in term_uses
                  if u["after"] < v["pos"] <= u["branch_end"]]
        if not inside:
            u["text"] = " _"
        elif u["name"] in EXIT_LIKE \
                and any(v["name"] not in EXIT_LIKE for v in inside) \
                and any(v["name"] in EXIT_LIKE for v in inside):
            # The branch of an exit says of a state, or of a continuation
            # or a function applied, that it comes to an exit: that is
            # done in the heap of the statement, not in the heap of the
            # exit matched, which gets another name; the exits of the
            # branch are given that one. (Where the branch has no exit
            # of its own it goes on from the exit matched, as a machine
            # does, and in its heap.)
            u["text"] = " " + HP + "'"
            for v in inside:
                if v["name"] in EXIT_LIKE:
                    v["text"] = " " + HP + "'"
            report.add(rel, line_of(t, u["start"]), "PATTERN-OUTER",
                       u["name"])
        u["anchor"] = None

    # two results matched together, whose exits are compared: the heaps
    # are compared too
    by_line = {}
    for u in uses:
        if u["pattern"] and u["name"] in EXIT_LIKE:
            by_line.setdefault(line_of(t, u["start"]), []).append(u)
    for ln, pair in by_line.items():
        if len(pair) != 2:
            continue
        u1, u2 = pair
        if not all(NAME_RE.fullmatch(x) for x in u1["args"] + u2["args"]):
            continue
        if "_" in u1["args"] + u2["args"]:
            continue
        bend = branch_end(doc, u2["after"])
        mm = re.compile(r"(?<![\w'])%s\s*=\s*%s(?![\w'])" % (
            re.escape(u1["args"][1]), re.escape(u2["args"][1]))).search(
                t, u2["after"], bend)
        if not mm:
            continue
        u1["text"] = " " + HP
        u2["text"] = " " + HP + "'"
        u1["branch_end"] = u2["branch_end"] = bend
        doc.insert(mm.end(), " ∧ %s = %s'" % (HP, HP), 4)
        report.add(rel, ln, "EXITS-COMPARED", "")

    # --- binders -------------------------------------------------------
    by_unit = {}
    for u in uses:
        if u["text"] == " " + HP and not u["pattern"]:
            by_unit.setdefault(u["unit"], []).append(u)
    # a use under a pattern that binds the heap needs no binder
    pattern_ranges = [(u["after"], u["branch_end"]) for u in uses
                      if u["pattern"] and u["text"] == " " + HP]

    def under_pattern(pos):
        return any(a < pos <= b for a, b in pattern_ranges)

    proof_units_needing = {}
    marked_all = {}
    section_heap = set()
    for ui, us in sorted(by_unit.items(), key=lambda kv: (kv[0] is None,
                                                         kv[0])):
        if ui is None:
            for u in us:
                report.add(rel, line_of(t, u["start"]), "NO-UNIT", u["name"])
            continue
        s, e, kw = units[ui]
        us = [u for u in us if not under_pattern(u["pos"])]
        if not us:
            continue
        if kw in ("Proof", "Qed", "Defined", "Admitted", "Abort"):
            proof_units_needing[ui] = us
            continue
        # sub-units of an inductive definition: one for each constructor
        subs = [(s, e)]
        cut_re = r"^with\s"
        if kw in ("Inductive", "CoInductive", "Variant"):
            cut_re = r"^with\s|^\s*\|\s+[A-Za-z_]"
        cuts = [mm.start() for mm in
                re.compile(cut_re, re.M).finditer(t, s, e)
                if not doc.mask[mm.start()]]
        mutual = False
        if cuts:
            bounds = [s] + cuts + [e]
            subs = list(zip(bounds[:-1], bounds[1:]))
            mutual = kw not in ("Inductive", "CoInductive", "Variant")

        def sub_of(pos):
            return next((i for i, (a, bb) in enumerate(subs)
                         if a <= pos < bb), 0)

        def scopes(bpos, upos):
            """Whether a binder at [bpos] scopes over [upos]."""
            if bpos > upos:
                return False
            st = paren_stack(doc, s, upos)
            st2 = paren_stack(doc, s, bpos)
            if st[:len(st2)] != st2:
                return False
            sb, su = sub_of(bpos), sub_of(upos)
            return sb == su or (sb == 0 and len(subs) > 1 and not mutual)

        binders = binders_in(doc, s, e)
        # the binder of the name beside each use, for the uses beside a
        # static environment first; then for the uses that no binder so
        # chosen scopes over
        keep = {}

        def covered(pos):
            return any(scopes(pos2, pos) for pos2 in keep)

        def binder_of(u):
            a = u["anchor"]
            if a is None or a[1] is None:
                return None
            for nm in a[1]:
                cands = [bb for bb in binders
                         if nm in bb["names"] and bb["pos"] < u["start"]
                         and scopes(bb["pos"], u["start"])]
                if cands:
                    return cands[-1], nm
            return None

        order = sorted(us, key=lambda u: (
            0 if (u["anchor"] and u["anchor"][0] == "statics") else 1,
            u["start"]))
        for u in order:
            a = u["anchor"]
            if a is None or a[1] is None or covered(u["start"]):
                continue
            found = binder_of(u)
            if found is None:
                continue
            b, nm = found
            b.setdefault("anchors", set()).add(nm)
            keep[b["pos"]] = b
        # drop a binder that is in the scope of another kept one
        for pos in sorted(keep):
            if any(pos2 != pos and scopes(pos2, pos) for pos2 in keep):
                del keep[pos]
        # An inner quantifier that binds a static environment binds its
        # own heap, where every state in its scope is built with a static
        # environment that it binds: what it says is said of a state that
        # runs later, in the heap of that time.
        inner = {}
        for u in us:
            a = u["anchor"]
            if a is None or a[0] != "statics":
                continue
            found = binder_of(u)
            if found is None or found[0]["pos"] in keep:
                continue
            inner.setdefault(found[0]["pos"],
                             (found[0], set()))[1].add(found[1])
        for pos in sorted(inner):
            b, nms = inner[pos]
            within = [u for u in us if scopes(pos, u["start"])]
            own = True
            for u in within:
                a = u["anchor"]
                if a is None or a[0] != "statics":
                    continue
                found = binder_of(u)
                if found is None or not (
                        found[0]["pos"] == pos
                        or scopes(pos, found[0]["pos"])):
                    own = False
            if not own:
                continue
            depth = sum(1 for pos2 in keep if scopes(pos2, pos))
            if depth == 0:
                continue
            hname = HP + "'" * depth
            b["anchors"] = set(nms) | b.get("anchors", set())
            b["heap_name"] = hname
            keep[pos] = b
            for u in within:
                u["text"] = " " + hname
            report.add(rel, line_of(t, pos), "BINDER-INNER", hname)
        # every use must be in the scope of a kept binder, or of a
        # variable of a section
        for u in us:
            if covered(u["start"]):
                continue
            a = u["anchor"]
            section_var = None
            if a and a[1]:
                for nm in a[1]:
                    for mm in re.finditer(
                            r"^(?:Variables?|Context)\s+\(?((?:[\w']+\s+)*"
                            + re.escape(nm) + r"(?:\s+[\w']+)*)\s*:\s*"
                            r"static_env\)?\.[ \t]*$", t[:s], re.M):
                        section_var = mm
                    if section_var:
                        break
            section_group = None
            if section_var is None and a and a[1]:
                # [Variables (statics : static_env) (x : t) ...]: several
                # groups in one sentence; the heap goes after the group
                # of the static environment
                for nm in a[1]:
                    for mm in re.finditer(
                            r"^(?:Variables?|Context)\s+(?:\([^()]*\)\s*)*?"
                            r"(\(\s*(?:[\w']+\s+)*" + re.escape(nm)
                            + r"(?:\s+[\w']+)*\s*:\s*static_env\s*\))",
                            t[:s], re.M):
                        section_group = mm
                    if section_group:
                        break
            if section_group is not None:
                if section_group.end(1) not in section_heap:
                    section_heap.add(section_group.end(1))
                    doc.insert(section_group.end(1),
                               " (%s : %s)" % (HP, HEAP_TYPE), 1)
                    report.add(rel, line_of(t, section_group.start()),
                               "SECTION-VARIABLE", "")
                continue
            if section_var is None and section_heap:
                continue
            if section_var is not None:
                if section_var.end() not in section_heap:
                    section_heap.add(section_var.end())
                    doc.insert(section_var.end(),
                               "\nVariable %s : %s." % (HP, HEAP_TYPE), 1)
                    report.add(rel, line_of(t, section_var.start()),
                               "SECTION-VARIABLE", "")
                continue
            if u["name"] in EXIT_LIKE and not NAME_RE.fullmatch(
                    u["args"][-1]):
                # an exit with given values, of a run from the empty heap
                u["text"] = " empty_heap"
                report.add(rel, line_of(t, u["start"]), "EXIT-EMPTY",
                           u["name"])
            elif u["name"] == "State" and kw in ("Definition", "Example"):
                # a state that an example builds
                u["text"] = " empty_heap"
                report.add(rel, line_of(t, u["start"]), "STATE-EMPTY",
                           u["name"])
            else:
                report.add(rel, line_of(t, u["start"]), "UNBOUND",
                           "%s: no binder in scope" % u["name"])
        hdr = parse_header(doc, s, e, kw) if kw in DECL_KW.split("|") else None
        for pos, b in keep.items():
            hname = b.get("heap_name", HP)
            if b["kind"] == "paren":
                doc.insert(b["close"] + 1, " (%s : %s)" % (hname, HEAP_TYPE),
                           1)
            elif b["kind"] == "brace":
                doc.insert(b["close"] + 1, " {%s : %s}" % (hname, HEAP_TYPE),
                           1)
            elif b["kind"] == "bare_typed":
                doc.insert(b["names_start"], "(", 1)
                doc.insert(b["stop"], ") (%s : %s)" % (hname, HEAP_TYPE), 1)
            else:
                ins = b["names_end"]
                for mm in NAME_RE.finditer(t, b["names_start"],
                                           b["names_end"]):
                    if mm.group(0) in b["anchors"]:
                        ins = mm.end()
                doc.insert(ins, " " + hname, 1)
            report.add(rel, line_of(t, pos), "BINDER", b["kind"])
            # where the binder is, for the intros and the applications
            if hdr is None:
                continue
            is_lemma = kw in LEMMA_KW
            is_stmt = kw == "Definition" and hdr["name"].endswith(
                "_statement")
            explicit_before = 0
            placed = False
            for (gpos, names, explicit) in hdr["header"]:
                if explicit:
                    explicit_before += len(names)
                if gpos == pos:
                    placed = True
                    if b["kind"] == "brace":
                        break  # implicit: no position changes
                    if is_lemma:
                        tables["lemma_arg"][hdr["name"]] = explicit_before
                        note_home(hdr["name"], pos)
                    else:
                        tables["def_arg"][hdr["name"]] = explicit_before
                        report.add(rel, line_of(t, pos), "DEF-ARG",
                                   "%s %d" % (hdr["name"], explicit_before))
                    break
            if placed:
                continue
            q = 0
            for (gpos, names) in hdr["leading"]:
                q += len(names)
                if b["kind"] == "paren":
                    in_group = gpos == pos
                elif b["kind"] == "bare_typed":
                    in_group = b["names_start"] <= gpos < b["stop"]
                    if in_group:
                        q = q - len(names) + len(b["names"])
                elif b["kind"] == "bare_untyped":
                    in_group = b["names_start"] <= gpos < b["names_end"]
                    if in_group:
                        qq = 0
                        for nm in b["names"]:
                            qq += 1
                            if nm in b["anchors"]:
                                break
                        q = q - len(names) + qq
                else:
                    in_group = False
                if in_group:
                    placed = True
                    if is_stmt:
                        tables["stmt_intro"][hdr["name"]] = q
                    elif is_lemma:
                        tables["lemma_arg"][hdr["name"]] = explicit_before + q
                        note_home(hdr["name"], pos)
                        marked_all[ui] = q
                    break
            if not placed:
                report.add(rel, line_of(t, pos), "BINDER-NESTED",
                           hdr["name"])

    for u in uses:
        doc.insert(u["pos"], u["text"], 5)
        if u["text"] != " _":
            report.add(rel, line_of(t, u["start"]), "USE", u["name"])
        else:
            report.add(rel, line_of(t, u["start"]), "USE-WILDCARD", u["name"])

    tables["proofs"][rel] = {
        "units": units, "marked": marked_all,
        "needing": {k: [(u["start"], u["anchor"]) for u in v]
                    for k, v in proof_units_needing.items()},
    }
    tables["docs"][rel] = doc
    return doc


INTROS_RE = re.compile(r"(?<![\w'])intros\b")


def patch_intros(doc, rel, s, e, q, report, who):
    """Insert the name after the [q]th pattern of the first [intros] of the
    proof in [s, e)."""
    t = doc.text
    # sentences before the first intros may only unfold
    m = INTROS_RE.search(t, s, e)
    while m and doc.mask[m.start()]:
        m = INTROS_RE.search(t, m.end(), e)
    if not m:
        report.add(rel, line_of(t, s), "INTROS-NONE", who)
        return False
    before = t[s:m.start()]
    before = re.sub(r"^Proof\.", "", before.strip())
    if before.strip() and not re.fullmatch(
            r"(\s*(unfold|red|cbn|simpl|hnf)\b[^.;]*[.;])*\s*", before):
        report.add(rel, line_of(t, m.start()), "INTROS-LATE", who)
        return False
    atoms = doc.read_atoms(m.end(), 200)
    if len(atoms) < q:
        report.add(rel, line_of(t, m.start()), "INTROS-SHORT",
                   "%s: %d names, binder at %d" % (who, len(atoms), q))
        return False
    doc.insert(atoms[q - 1][1], " " + HP, 2)
    report.add(rel, line_of(t, m.start()), "INTROS", who)
    return True


def phase1b(tables, report):
    """The intros of the proofs, and the patterns of the proofs that build
    a state."""
    for rel, info in tables["proofs"].items():
        doc = tables["docs"][rel]
        t = doc.text
        units = info["units"]
        for ui, (s, e, kw) in enumerate(units):
            if kw not in LEMMA_KW and kw != "Instance":
                continue
            # the proof is the next unit
            if ui + 1 >= len(units) or units[ui + 1][2] != "Proof":
                continue
            ps, pe, _ = units[ui + 1]
            q = info["marked"].get(ui)
            bound = False
            if q is not None:
                patch_intros(doc, rel, ps, pe, q, report, "own statement")
                bound = True
            else:
                # [Theorem foo : X_statement.]
                m = re.compile(
                    r"\s+([A-Za-z_][\w']*)\s*:\s*([A-Za-z_][\w'.]*)\s*\.\s*$"
                ).search(t[s:ps])
                if m:
                    stmt = m.group(2).split(".")[-1]
                    if stmt in tables["stmt_intro"]:
                        q = tables["stmt_intro"][stmt]
                        patch_intros(doc, rel, ps, pe, q, report, stmt)
                        tables["lemma_arg"][m.group(1)] = q
                        bound = True
            need = info["needing"].get(ui + 1)
            if not bound:
                # the statement may have gained a binder elsewhere (in
                # its header, or nested)
                bound = any(s <= p < ps and order == 1
                            for (p, order, _) in doc.inserts)
            if need and not bound:
                anchors = {nm for (_, a) in need if a and a[1]
                           for nm in a[1][:1]}
                done = False
                for mm in re.compile(r"\[([A-Za-z_][\w']*(?:\s+[A-Za-z_]"
                                     r"[\w']*){3})\]").finditer(t, ps, pe):
                    if doc.mask[mm.start()]:
                        continue
                    names = mm.group(1).split()
                    if names[3] in anchors:
                        doc.insert(mm.end() - 1, " " + HP, 2)
                        report.add(rel, line_of(t, mm.start()), "PATTERN",
                                   names[3])
                        done = True
                if not done:
                    report.add(rel, line_of(t, need[0][0]), "PROOF-NO-HEAP",
                               "a state is built and no heap is named")


def phase2(doc, rel, tables, report):
    """Explicit applications of the lemmas that gained an argument."""
    t = doc.text
    names = {n: p for n, p in tables["lemma_arg"].items()}
    if not names:
        return doc
    decl_re = re.compile(r"(?:" + DECL_KW + r")\s+$")
    count = 0
    units = tables["proofs"][rel]["units"]
    starts = [u[0] for u in units]
    import bisect
    for m in target_regex(names).finditer(t):
        if doc.mask[m.start()]:
            continue
        name = m.group(1)
        if in_name_list(t, m.start()):
            continue
        # in a proof script only
        ui = bisect.bisect_right(starts, m.start()) - 1
        if ui < 0 or units[ui][2] not in ("Proof", "Ltac", "Tactic"):
            continue
        if decl_re.search(t[max(0, m.start() - 40):m.start()]):
            continue
        p = names[name]
        atoms = doc.read_atoms(m.end(), p + 1)
        if len(atoms) <= p:
            continue
        home = tables["lemma_home"].get(name)
        if home and not (home[0] == rel and home[1] <= m.start() < home[2]):
            report.add(rel, line_of(t, m.start()), "APPLICATION-OUTSIDE",
                       name)
            continue
        pos = atoms[p - 1][1] if p > 0 else m.end()
        fill = " " + HP if name in tables["def_arg"] else " _"
        doc.insert(pos, fill, 3)
        count += 1
        report.add(rel, line_of(t, m.start()), "APPLICATION", name)
    return doc


def main():
    root = sys.argv[1]
    report_path = None
    if "--report" in sys.argv:
        report_path = sys.argv[sys.argv.index("--report") + 1]
    if "--extra" in sys.argv:
        with open(sys.argv[sys.argv.index("--extra") + 1]) as f:
            EXTRA.update(json.load(f))
    dirs = ["middle_end/flambda2/rocq", "middle_end/flambda2/types/rocq"]
    files = []
    for d in dirs:
        for fn in sorted(os.listdir(os.path.join(root, d))):
            if fn.endswith(".v"):
                files.append(os.path.join(d, fn))
    # Spec files first: their statements give the proofs their positions
    files.sort(key=lambda p: (not p.endswith("Spec.v"), p))
    # A definition that gains the heap because its body builds a state is
    # itself a name whose uses gain the heap: the first phase is run again
    # until no such definition is new.
    for _ in range(6):
        report = Report()
        tables = {"lemma_arg": {}, "def_arg": {}, "stmt_intro": {},
                  "proofs": {}, "docs": {}, "lemma_home": {}}
        for rel in files:
            process_file(os.path.join(root, rel), rel, tables, report, 1)
        new = {n: p for n, p in tables["def_arg"].items()
               if n not in TARGETS and n not in EXTRA}
        if not new:
            break
        EXTRA.update(new)
        print("definitions that gain the heap:", sorted(new.items()))
    phase1b(tables, report)
    for rel in files:
        doc = tables["docs"][rel]
        phase2(doc, rel, tables, report)
    changed = 0
    for rel in files:
        doc = tables["docs"][rel]
        new = doc.result()
        if new != doc.text:
            changed += 1
            with open(os.path.join(root, rel), "w", encoding="utf-8") as f:
                f.write(new)
    if report_path:
        with open(report_path, "w") as f:
            for row in sorted(report.rows):
                f.write("%s\t%s\t%s\t%s\n" % row)
        with open(report_path + ".tables.json", "w") as f:
            json.dump({k: tables[k] for k in ("lemma_arg", "def_arg",
                                               "stmt_intro")}, f, indent=1,
                      sort_keys=True)
    print("files changed:", changed)
    counts = {}
    for (_, _, cls, _) in report.rows:
        counts[cls] = counts.get(cls, 0) + 1
    for cls in sorted(counts):
        print("%-16s %d" % (cls, counts[cls]))


if __name__ == "__main__":
    main()
