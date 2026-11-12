#!/usr/bin/env python3
"""Writes one random small OCaml unit, X.ml and X.mli, in the fragment that
the Rocq model of Flambda 2 has: integers, booleans, a variant, options,
pairs, a record, closures and inlined helper functions, and, in two of the
profiles, exception handlers, loops on references and recursive functions,
with no standard library.

    gen.py SEED PROFILE DIR

PROFILE is one of
  known      every input is a constant;
  unknown    some inputs are behind [opaque];
  functions  as unknown, and the unit keeps a function that is not inlined;
  exceptions as unknown, with handlers, raises and divisions;
  loops      as unknown, with [for] and [while] loops on references and
             recursive functions, one of which the unit keeps;
with _scalar added (known_scalar, ...) for a unit whose results are integers
and booleans only, so that no block is left for Simplify to make a symbol.
See README.md."""
import random, sys, os

seed = int(sys.argv[1]); profile = sys.argv[2]; outdir = sys.argv[3]
scalar = profile.endswith('_scalar')
profile = profile.replace('_scalar', '')
rnd = random.Random(seed * 7919 + {'known': 1, 'unknown': 2, 'functions': 3, 'exceptions': 4, 'loops': 5}[profile] + (10 if scalar else 0))
EXN = profile == 'exceptions'
LOOPS = profile == 'loops'

PRELUDE = '''external ( + ) : int -> int -> int = "%addint"
external ( - ) : int -> int -> int = "%subint"
external ( * ) : int -> int -> int = "%mulint"
external ( land ) : int -> int -> int = "%andint"
external ( lor ) : int -> int -> int = "%orint"
external ( lxor ) : int -> int -> int = "%xorint"
external ( < ) : int -> int -> bool = "%lessthan"
external ( <= ) : int -> int -> bool = "%lessequal"
external ( > ) : int -> int -> bool = "%greaterthan"
external ( = ) : int -> int -> bool = "%equal"
external ( <> ) : int -> int -> bool = "%notequal"
external not : bool -> bool = "%boolnot"
external ( && ) : bool -> bool -> bool = "%sequand"
external ( || ) : bool -> bool -> bool = "%sequor"
external opaque : 'a -> 'a = "%opaque"
type 'a option = None | Some of 'a
type t = A | B of int | C of int * int | D
type r = { x : int; y : int }
'''
if EXN:
    PRELUDE += '''external ( / ) : int -> int -> int = "%divint"
external ( mod ) : int -> int -> int = "%modint"
external raise : exn -> 'a = "%raise"
external raise_notrace : exn -> 'a = "%raise_notrace"
'''
if LOOPS:
    PRELUDE += '''type 'a ref = { mutable contents : 'a }
external ref : 'a -> 'a ref = "%makemutable"
external ( ! ) : 'a ref -> 'a = "%field0"
external ( := ) : 'a ref -> 'a -> unit = "%setfield0"
'''
TYPES_MLI = '''type 'a option = None | Some of 'a
type t = A | B of int | C of int * int | D
type r = { x : int; y : int }
'''
OCAML_TYPE = {'int': 'int', 'bool': 'bool', 'opt': 'int option', 'pair': 'int * int', 't': 't', 'r': 'r', 'fn': 'int -> int'}
counter = [0]
def fresh(p='v'):
    counter[0] += 1
    return '%s%d' % (p, counter[0])

P_OPAQUE = {'known': 0.0, 'unknown': 0.25, 'functions': 0.15, 'exceptions': 0.25, 'loops': 0.25}[profile]
# The number of handlers around the expression being written, and of loops.
in_try = [0]
in_loop = [0]

def lit():
    n = rnd.randint(-3, 9)
    s = str(n) if n >= 0 else '(%d)' % n
    if rnd.random() < P_OPAQUE:
        return '(opaque %s)' % s
    return s

def var(env, ty):
    vs = [n for n, t in env if t == ty]
    if vs and rnd.random() < 0.6:
        return rnd.choice(vs)
    return None

def gen(env, ty, d):
    return GEN[ty](env, d)

def small():
    n = rnd.randint(0, 6)
    if rnd.random() < P_OPAQUE:
        return '(opaque %d)' % n
    return str(n)

def g_exn_int(env, d):
    c = rnd.random()
    if in_try[0] == 0 or c < 0.3:
        in_try[0] += 1
        body = g_int(env, d - 1)
        in_try[0] -= 1
        return '(try %s with _ -> %s)' % (body, g_int(env, d - 1))
    if c < 0.55:
        r = rnd.choice(['raise', 'raise', 'raise_notrace'])
        return '(if %s then %s Not_found else %s)' % (g_bool(env, d - 1), r, g_int(env, d - 1))
    op = rnd.choice(['/', 'mod'])
    return '(%s %s %s)' % (g_int(env, d - 1), op, g_int(env, d - 1))

def g_loop_int(env, d):
    c = rnd.random()
    in_loop[0] += 1
    acc = fresh('acc')
    if c < 0.3:
        i = fresh('i')
        body = g_int(env + [(i, 'int'), ('!' + acc, 'int')], d - 1)
        down = rnd.random() < 0.25
        lo, hi = small(), small()
        r = '(let %s = ref %s in for %s = %s %s %s do %s := %s done; !%s)' % (
            acc, lit(), i, hi if down else lo, 'downto' if down else 'to',
            lo if down else hi, acc, body, acc)
    elif c < 0.55:
        i = fresh('i')
        body = g_int(env + [('!' + i, 'int'), ('!' + acc, 'int')], d - 1)
        r = ('(let %s = ref 0 in let %s = ref %s in while !%s < %s do %s := %s; %s := !%s + 1 done; !%s)'
             % (i, acc, lit(), i, small(), acc, body, i, i, acc))
    elif c < 0.8:
        go, n = fresh('go'), fresh('n')
        body = g_int(env + [(n, 'int'), (acc, 'int')], d - 1)
        r = '(let rec %s %s %s = if %s <= 0 then %s else %s (%s - 1) %s in %s %s %s)' % (
            go, n, acc, n, acc, go, n, body, go, small(), lit())
    else:
        go, n = fresh('go'), fresh('n')
        body = g_int(env + [(n, 'int'), (acc, 'int')], d - 1)
        r = '(let rec %s %s = if %s <= 0 then %s else (let %s = %s (%s - 1) in %s) in %s %s)' % (
            go, n, n, lit(), acc, go, n, body, go, small())
    in_loop[0] -= 1
    return r

def g_int(env, d):
    v = var(env, 'int')
    if d <= 0:
        return v or lit()
    if EXN and rnd.random() < 0.2:
        return g_exn_int(env, d)
    if LOOPS and in_loop[0] < 2 and rnd.random() < 0.2:
        return g_loop_int(env, d)
    c = rnd.random()
    if c < 0.12: return v or lit()
    if c < 0.34:
        op = rnd.choice(['+', '-', '*', 'land', 'lor', 'lxor'])
        return '(%s %s %s)' % (g_int(env, d - 1), op, g_int(env, d - 1))
    if c < 0.46:
        return '(if %s then %s else %s)' % (g_bool(env, d - 1), g_int(env, d - 1), g_int(env, d - 1))
    if c < 0.58:
        a, b = fresh('a'), fresh('b')
        return '(match %s with A -> %s | B %s -> %s | C (%s, %s) -> %s | D -> %s)' % (
            g_t(env, d - 1), g_int(env, d - 1), a, g_int(env + [(a, 'int')], d - 1),
            a, b, g_int(env + [(a, 'int'), (b, 'int')], d - 1), g_int(env, d - 1))
    if c < 0.66:
        a = fresh('a')
        return '(match %s with None -> %s | Some %s -> %s)' % (
            g_opt(env, d - 1), g_int(env, d - 1), a, g_int(env + [(a, 'int')], d - 1))
    if c < 0.74:
        a, b = fresh('a'), fresh('b')
        return '(match %s with (%s, %s) -> %s)' % (
            g_pair(env, d - 1), a, b, g_int(env + [(a, 'int'), (b, 'int')], d - 1))
    if c < 0.80:
        return '(%s).%s' % (g_r(env, d - 1), rnd.choice(['x', 'y']))
    if c < 0.90:
        return '(%s %s)' % (g_fn(env, d - 1), g_int(env, d - 1))
    return g_let(env, d, 'int')

def g_bool(env, d):
    v = var(env, 'bool')
    if d <= 0:
        return v or rnd.choice(['true', 'false'])
    c = rnd.random()
    if c < 0.1: return v or rnd.choice(['true', 'false'])
    if c < 0.6:
        op = rnd.choice(['<', '<=', '>', '=', '<>'])
        return '(%s %s %s)' % (g_int(env, d - 1), op, g_int(env, d - 1))
    if c < 0.75: return '(%s && %s)' % (g_bool(env, d - 1), g_bool(env, d - 1))
    if c < 0.9: return '(%s || %s)' % (g_bool(env, d - 1), g_bool(env, d - 1))
    return '(not %s)' % g_bool(env, d - 1)

def g_opt(env, d):
    v = var(env, 'opt')
    if d <= 0: return v or rnd.choice(['None', '(Some %s)' % lit()])
    c = rnd.random()
    if c < 0.15: return v or 'None'
    if c < 0.25: return 'None'
    if c < 0.7: return '(Some %s)' % g_int(env, d - 1)
    if c < 0.9: return '(if %s then %s else %s)' % (g_bool(env, d - 1), g_opt(env, d - 1), g_opt(env, d - 1))
    return g_let(env, d, 'opt')

def g_pair(env, d):
    v = var(env, 'pair')
    if d <= 0: return v or '(%s, %s)' % (lit(), lit())
    c = rnd.random()
    if c < 0.15: return v or '(1, 2)'
    if c < 0.8: return '(%s, %s)' % (g_int(env, d - 1), g_int(env, d - 1))
    return g_let(env, d, 'pair')

def g_t(env, d):
    v = var(env, 't')
    if d <= 0: return v or rnd.choice(['A', 'D', '(B %s)' % lit(), '(C (%s, %s))' % (lit(), lit())])
    c = rnd.random()
    if c < 0.15: return v or 'A'
    if c < 0.25: return rnd.choice(['A', 'D'])
    if c < 0.5: return '(B %s)' % g_int(env, d - 1)
    if c < 0.75: return '(C (%s, %s))' % (g_int(env, d - 1), g_int(env, d - 1))
    if c < 0.9: return '(if %s then %s else %s)' % (g_bool(env, d - 1), g_t(env, d - 1), g_t(env, d - 1))
    return g_let(env, d, 't')

def g_r(env, d):
    v = var(env, 'r')
    if d <= 0 or rnd.random() < 0.2: return v or '{ x = %s; y = %s }' % (lit(), lit())
    return '{ x = %s; y = %s }' % (g_int(env, d - 1), g_int(env, d - 1))

def g_fn(env, d):
    v = var(env, 'fn')
    if v and rnd.random() < 0.5: return v
    z = fresh('z')
    return '(fun [@inline] %s -> %s)' % (z, g_int(env + [(z, 'int')], max(d - 1, 0)))

def g_let(env, d, ty):
    bty = rnd.choice(['int', 'int', 'bool', 'opt', 'pair', 't', 'r', 'fn'])
    x = fresh('x')
    return '(let %s = %s in %s)' % (x, gen(env, bty, d - 1), gen(env + [(x, bty)], ty, d - 1))

GEN = {'int': g_int, 'bool': g_bool, 'opt': g_opt, 'pair': g_pair, 't': g_t, 'r': g_r, 'fn': g_fn}

out = [PRELUDE]
mli = [TYPES_MLI]
helpers = []
for i in range(rnd.randint(1, 3)):
    name = 'h%d' % i
    rty = rnd.choice(['int', 'int', 'bool', 'opt', 'pair', 't', 'r'])
    env = [('p', 'int'), ('q', 'int'), ('b', 'bool')]
    raises = EXN and rnd.random() < 0.4
    if raises:
        in_try[0] += 1
    out.append('let[@inline] %s (p : int) (q : int) (b : bool) : %s = %s' % (name, OCAML_TYPE[rty], gen(env, rty, 3)))
    if raises:
        in_try[0] -= 1
    helpers.append((name, rty, raises))
if profile == 'functions':
    for i in range(rnd.randint(1, 2)):
        name = 'f%d' % i
        env = [('p', 'int'), ('q', 'int')]
        out.append('let %s : int -> int -> int = fun p q -> %s' % (name, g_int(env, 3)))
        mli.append('val %s : int -> int -> int' % name)
        helpers.append((name, 'fun2', False))
if LOOPS:
    env = [('n', 'int'), ('acc', 'int')]
    in_loop[0] += 1
    if rnd.random() < 0.6:
        out.append('let rec f0 n acc = if n <= 0 then acc else f0 (n - 1) %s' % g_int(env, 2))
    else:
        out.append('let rec f0 n acc = if n <= 0 then acc else (let acc = f0 (n - 1) acc in %s)' % g_int(env, 2))
    in_loop[0] -= 1
    mli.append('val f0 : int -> int -> int')
    helpers.append(('f0', 'rec2', False))
for i in range(rnd.randint(1, 3)):
    name = 'result%d' % i
    ty = rnd.choice(['int', 'int', 'int', 'bool'] if scalar else ['int', 'int', 'int', 'bool', 'opt', 'pair', 't'])
    env = []
    lets = []
    for (h, rty, raises) in helpers:
        x = fresh('x')
        if rty == 'fun2':
            lets.append('let %s = %s %s %s in' % (x, h, lit(), lit()))
            env.append((x, 'int'))
        elif rty == 'rec2':
            lets.append('let %s = %s %s %s in' % (x, h, small(), lit()))
            env.append((x, 'int'))
        elif raises:
            call = '%s %s %s %s' % (h, lit(), lit(), rnd.choice(['true', 'false']))
            lets.append('let %s = try %s with _ -> %s in' % (x, call, gen([], rty, 0)))
            env.append((x, rty))
        else:
            lets.append('let %s = %s %s %s %s in' % (x, h, lit(), lit(), rnd.choice(['true', 'false'])))
            env.append((x, rty))
    out.append('let %s : %s = %s %s' % (name, OCAML_TYPE[ty], ' '.join(lets), gen(env, ty, rnd.randint(2, 4))))
    mli.append('val %s : %s' % (name, OCAML_TYPE[ty]))
base = os.path.join(outdir, 'c_%s_%04d' % (profile + ('_scalar' if scalar else ''), seed))
open(base + '.ml', 'w').write('\n'.join(out) + '\n')
open(base + '.mli', 'w').write('\n'.join(mli) + '\n')
