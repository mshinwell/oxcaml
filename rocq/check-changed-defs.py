#!/usr/bin/env python3
# Usage, from the root of a worktree:
#   check-changed-defs.py BASE TIP [MAX]
#   check-changed-defs.py --reach REV NAME [MAX]
#
# The first form, for the range BASE..TIP: the definitions of *Spec.v
# files (and of FlambdaModel.v, FlambdaPrimitiveModel.v and
# FlambdaKindModel.v) whose body differs between BASE and TIP and that
# are not statements, and for each the statements
# (Definition ..._statement) of TIP in which its name occurs, directly
# or through other definitions of those files. The second form: the
# statements of REV in which the one definition NAME occurs, directly
# or through other definitions. Where a definition reaches more than
# MAX statements (40 if not given) only the count is printed for those
# reached through other definitions.
#
# A search over names, not a judgement. A definition is identified by
# its file and its name, so two files that each define a name are two
# entries. An occurrence is of the name as a word, with comments
# removed, in any file: where two files define one name, a use of the
# name counts for both (the search may list too much, never too little
# for that reason). An item is the sentence that begins at its keyword:
# text between its full stop and the next item is not compared.
#
# FlambdaKindModel.v and FlambdaPrimitiveModel.v import no other file of
# the model, so an item of theirs is searched for the names that those
# two files define and for no other: a constructor argument named as a
# definition of a later file is not a use of that definition. As long
# as no name is defined both in the two files and elsewhere, what a
# definition of any other file reaches is what it reached before the
# two files were read; what they add is their own definitions, with
# what each reaches. The search tests both conditions on the commit that
# it reads and says so first where one fails.
import re, subprocess, sys, collections
reach = len(sys.argv) > 1 and sys.argv[1] == '--reach'
args = sys.argv[2:] if reach else sys.argv[1:]
if len(args) < 2:
    sys.exit('usage: check-changed-defs.py BASE TIP [MAX] | --reach REV NAME [MAX]')
MAX = int(args[2]) if len(args) > 2 else 40
def git(*a):
    return subprocess.check_output(('git',) + a).decode('utf-8', 'replace')
LEAVES = ('FlambdaKindModel.v', 'FlambdaPrimitiveModel.v')
def short(f):
    return f.split('/')[-1]
def spec_files(rev):
    out = git('ls-tree', '-r', '--name-only', rev, '--', 'middle_end/flambda2', 'rocq')
    return [f for f in out.split('\n')
            if f.endswith('Spec.v') or f.endswith('/FlambdaModel.v')
            or short(f) in LEAVES]
def strip_comments(s):
    out, depth, i, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith('(*', i):
            depth += 1; i += 2
        elif s.startswith('*)', i) and depth > 0:
            depth -= 1; i += 2
        else:
            if depth == 0:
                out.append(s[i])
            elif s[i] == '\n':
                out.append('\n')
            i += 1
    return ''.join(out)
head = re.compile(r'^(?:Local |Global |#\[[^\]]*\]\s*)?(?:Definition|Fixpoint|Inductive|Record|Variant|CoInductive|CoFixpoint|Function|Notation|Lemma|Theorem|Instance|Class|Axiom|Parameter)\s+([A-Za-z_][A-Za-z0-9_\']*)', re.M)
sentence_end = re.compile(r'(?<!\.)\.(?=\s|$)')
proof_start = re.compile(r'\s*Proof\b')
proof_end = re.compile(r'\b(?:Qed|Defined|Admitted)\.')
def items(rev):
    res = {}
    for f in spec_files(rev):
        try:
            text = strip_comments(git('show', rev + ':' + f))
        except subprocess.CalledProcessError:
            continue
        ms = list(head.finditer(text))
        for k, m in enumerate(ms):
            end = ms[k + 1].start() if k + 1 < len(ms) else len(text)
            # An item is one sentence: it ends at the first full stop
            # that is followed by white space. What comes after it and
            # before the next item (End, Section, Variable, Import)
            # is not part of it.
            stop = sentence_end.search(text, m.end(), end)
            if stop:
                # ... unless a proof script follows (a definition made
                # by tactics): then it ends where the script does.
                script = proof_start.match(text, stop.end(), end)
                close = proof_end.search(text, script.end(), end) if script else None
                end = close.end() if close else stop.end()
            body = re.sub(r'\s+', ' ', text[m.start():end]).strip()
            names = [m.group(1)]
            if re.match(r'(?:Local |Global )?(?:Fixpoint|Inductive|CoInductive|CoFixpoint)\b', body):
                names += re.findall(r'\bwith ([A-Za-z_][A-Za-z0-9_\']*)\b', body)
            for nm in names:
                key = (short(f), nm)
                # a name defined twice in one file (sections): keep both bodies
                res[key] = res[key] + ' ;; ' + body if key in res else body
    return res
def leaves_condition(rev, new):
    # The two things that the rule for LEAVES rests on.
    notes = []
    leaf_names = set(k[1] for k in new if k[0] in LEAVES)
    for k in sorted(new):
        if k[0] not in LEAVES and k[1] in leaf_names:
            notes.append('%s is defined in %s and in one of %s'
                         % (k[1], k[0], ' and '.join(LEAVES)))
    for f in spec_files(rev):
        if short(f) in LEAVES:
            text = strip_comments(git('show', rev + ':' + f))
            for m in re.finditer(r'\bRequire\s+(?:Import|Export)\s+([^.]*)\.', text):
                for mod in m.group(1).split():
                    if mod.startswith('Flambda') and mod + '.v' not in LEAVES:
                        notes.append('%s imports %s' % (short(f), mod))
    for n in notes:
        print('!! the items of %s are searched for their own names only, and %s'
              % (' and '.join(LEAVES), n))
def is_stmt(key):
    return key[1].endswith('_statement')
word = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
def index(new):
    defined_names = collections.defaultdict(list)
    for k in new:
        defined_names[k[1]].append(k)
    # users[name] = the items whose body mentions the name
    users = collections.defaultdict(set)
    leaf_names = set(k[1] for k in new if k[0] in LEAVES)
    for k, b in new.items():
        for w in set(word.findall(b)):
            if w in defined_names and w != k[1]:
                if k[0] in LEAVES and w not in leaf_names:
                    continue
                users[w].add(k)
    return defined_names, users
def reached(users, starts):
    direct = set()
    for d in starts:
        direct |= set(u for u in users[d[1]] if is_stmt(u))
    seen, frontier, through = set(starts), list(starts), set()
    while frontier:
        nxt = []
        for x in frontier:
            for u in users[x[1]]:
                if u in seen:
                    continue
                seen.add(u)
                if is_stmt(u):
                    through.add(u)
                else:
                    nxt.append(u)
        frontier = nxt
    return sorted(direct), sorted(through - direct)
if reach:
    rev, name = args[0], args[1]
    new = items(rev)
    leaves_condition(rev, new)
    defined_names, users = index(new)
    starts = defined_names[name]
    if not starts:
        sys.exit('no definition named ' + name)
    direct, indirect = reached(users, starts)
    show = lambda k: '%s (%s)' % (k[1], k[0])
    print('%s: defined in %s' % (name, ', '.join(k[0] for k in starts)))
    print('directly in %d:' % len(direct))
    for k in direct:
        print('  ', show(k))
    print('through other definitions in %d:' % len(indirect))
    if len(direct) + len(indirect) <= MAX:
        for k in indirect:
            print('  ', show(k))
    else:
        by_file = collections.Counter(k[0] for k in indirect)
        for f, n in sorted(by_file.items(), key=lambda x: (-x[1], x[0])):
            print('  %4d  %s' % (n, f))
    sys.exit(0)
base, tip = args[0], args[1]
old, new = items(base), items(tip)
leaves_condition(tip, new)
changed = sorted(k for k in new if not is_stmt(k) and k in old and old[k] != new[k])
added = sorted(k for k in new if not is_stmt(k) and k not in old)
removed = sorted(k for k in old if not is_stmt(k) and k not in new)
changed_statements = sorted(k for k in new if is_stmt(k) and k in old and old[k] != new[k])
added_statements = sorted(k for k in new if is_stmt(k) and k not in old)
removed_statements = sorted(k for k in old if is_stmt(k) and k not in new)
defined_names, users = index(new)
def show(k):
    return '%s (%s)' % (k[1], k[0]) if len(defined_names[k[1]]) > 1 else k[1]
def names(ks):
    return ', '.join(show(k) for k in ks)
print('== statements whose text changes:', names(changed_statements) or 'none')
print('== statements added:', names(added_statements) or 'none')
print('== statements removed:', ', '.join('%s (%s)' % (k[1], k[0]) for k in removed_statements) or 'none')
print('== definitions added:', ', '.join('%s (%s)' % (k[1], k[0]) for k in added) or 'none')
print('== definitions removed:', ', '.join('%s (%s)' % (k[1], k[0]) for k in removed) or 'none')
print('== %d definitions whose body changes, and the statements of the tip in which each occurs' % len(changed))
for d in changed:
    direct, indirect = reached(users, [d])
    total = len(direct) + len(indirect)
    clash = '' if len(defined_names[d[1]]) == 1 else \
        '  [the name is also defined in: %s]' % ', '.join(k[0] for k in defined_names[d[1]] if k != d)
    print('%s  (%s)  reaches %d%s' % (d[1], d[0], total, clash))
    if total <= MAX:
        print('   directly in %d: %s' % (len(direct), names(direct)))
        print('   through other definitions in %d: %s' % (len(indirect), names(indirect)))
    else:
        print('   directly in %d: %s' % (len(direct), names(direct[:MAX]) + (' ...' if len(direct) > MAX else '')))
        print('   through other definitions in %d statements (more than %d in all: not listed)' % (len(indirect), MAX))
