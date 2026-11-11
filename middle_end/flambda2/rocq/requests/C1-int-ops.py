#!/usr/bin/env python3
"""Generates an .fl file that checks the integer primitives of one kind
against a reference written here on Python's unbounded integers. It goes with
the request C1-primitives.md and is not part of any build.

Each check computes one primitive on two numbers and compares the result with
the reference. The term returns a block with one field for each check, which
is 1 where the two agree. Run by flsemantics, every field is 1 before
Simplify if the model agrees with the reference, and after Simplify, which
folds everything, if Simplify agrees with it.

Usage: C1-int-ops.py KIND NAME [full | small | V1,V2,... [OP,OP,...]]
writes NAME.fl to standard output; KIND is one of the keys of KINDS, and the
numbers default to fourteen that include the bounds of the kind. A list of
numbers that begins with a negative one needs a leading space."""
import sys

KINDS = {
    # name: (width, flag, literal suffix)
    "tagged": (63, None, ""),
    "imm": (63, "imm", "i"),
    "int8": (8, "int8", "s"),
    "int16": (16, "int16", "S"),
    "int32": (32, "int32", "l"),
    "int64": (64, "int64", "L"),
    "nativeint": (64, "nativeint", "n"),
}

def wrap(w, z):
    return (z + (1 << (w - 1))) % (1 << w) - (1 << (w - 1))

def unsigned(w, z):
    return z + (1 << w) if z < 0 else z

def trunc_div(a, b):
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q

def trunc_rem(a, b):
    return a - b * trunc_div(a, b)

ARITH = {
    "add": lambda w, a, b: wrap(w, a + b),
    "sub": lambda w, a, b: wrap(w, a - b),
    "mul": lambda w, a, b: wrap(w, a * b),
    "div": lambda w, a, b: None if b == 0 else wrap(w, trunc_div(a, b)),
    "mod": lambda w, a, b: None if b == 0 else wrap(w, trunc_rem(a, b)),
    "udiv": lambda w, a, b: None if b == 0
        else wrap(w, unsigned(w, a) // unsigned(w, b)),
    "umod": lambda w, a, b: None if b == 0
        else wrap(w, unsigned(w, a) % unsigned(w, b)),
    "and": lambda w, a, b: wrap(w, a & b),
    "or": lambda w, a, b: wrap(w, a | b),
    "xor": lambda w, a, b: wrap(w, a ^ b),
}

def sign(x):
    return (x > 0) - (x < 0)

COMP = {
    "`eq`": lambda w, a, b: int(a == b),
    "`ne`": lambda w, a, b: int(a != b),
    "`lt`": lambda w, a, b: int(a < b),
    "`le`": lambda w, a, b: int(a <= b),
    "`gt`": lambda w, a, b: int(a > b),
    "`ge`": lambda w, a, b: int(a >= b),
    "`qmark`": lambda w, a, b: sign(a - b),
    "`unsigned`.`lt`": lambda w, a, b: int(unsigned(w, a) < unsigned(w, b)),
    "`unsigned`.`le`": lambda w, a, b: int(unsigned(w, a) <= unsigned(w, b)),
    "`unsigned`.`gt`": lambda w, a, b: int(unsigned(w, a) > unsigned(w, b)),
    "`unsigned`.`ge`": lambda w, a, b: int(unsigned(w, a) >= unsigned(w, b)),
    "`unsigned`.`qmark`":
        lambda w, a, b: sign(unsigned(w, a) - unsigned(w, b)),
}

def main():
    kind, name = sys.argv[1], sys.argv[2]
    values_arg = sys.argv[3] if len(sys.argv) > 3 else "full"
    w, flag, suffix = KINDS[kind]
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    only = None
    if values_arg == "full":
        values = [lo, lo + 1, -100, -7, -2, -1, 0, 1, 2, 3, 13, 100, hi - 1,
                  hi]
    elif values_arg == "small":
        values = [lo, -7, -1, 0, 1, 13, hi]
    else:
        values = [int(v) for v in values_arg.split(",")]
        only = sys.argv[4].split(",") if len(sys.argv) > 4 else None
    values = sorted(set(v for v in values if lo <= v <= hi))
    prefix = "" if flag is None else "`%s`." % flag
    out = []
    counter = [0]
    def fresh(base):
        counter[0] += 1
        return "%s%d" % (base, counter[0])
    # A literal has to fit OCaml's [int] whatever its kind, so the numbers
    # beyond 63 bits are computed, by a multiplication that does not wrap.
    names = {}
    def literal(v):
        return "%d%s" % (v, suffix)
    def operand(v):
        if -(1 << 62) <= v <= (1 << 62) - 1:
            return literal(v)
        if v not in names:
            x = fresh("big")
            if v == lo:
                out.append("let %s = %%int_barith.%s`mul` (%s, %s) in"
                           % (x, prefix, literal(lo // 2), literal(2)))
            else:
                # v = 2 * (v // 2) + (v % 2), computed without wrapping
                half = fresh("half")
                out.append("let %s = %%int_barith.%s`mul` (%s, %s) in"
                           % (half, prefix, literal(v // 2), literal(2)))
                out.append("let %s = %%int_barith.%s`add` (%s, %s) in"
                           % (x, prefix, half, literal(v % 2)))
            names[v] = x
        return names[v]
    results = []
    def check(compute, compare):
        r, c, t = fresh("r"), fresh("c"), fresh("t")
        out.append("let %s = %s in" % (r, compute))
        out.append("let %s = %s in" % (c, compare(r)))
        out.append("let %s = %%tag_imm (%s) in" % (t, c))
        results.append(t)
    ops = ARITH if only is None else {k: ARITH[k] for k in only if k in ARITH}
    comps = COMP if only is None else {k: COMP[k] for k in only if k in COMP}
    for a in values:
        for b in values:
            for op, f in ops.items():
                expected = f(w, a, b)
                if expected is None:
                    continue
                check("%%int_barith.%s`%s` (%s, %s)"
                      % (prefix, op, operand(a), operand(b)),
                      lambda r, e=operand(expected):
                          "%%int_comp.%s`eq` (%s, %s)" % (prefix, r, e))
            for op, f in comps.items():
                expected = f(w, a, b)
                check("%%int_comp.%s%s (%s, %s)"
                      % (prefix, op, operand(a), operand(b)),
                      lambda r, e=expected:
                          "%%int_comp.`imm`.`eq` (%s, %di)" % (r, e))
    rows = [", ".join(results[i:i + 10]) for i in range(0, len(results), 10)]
    out.append("let $caml%s =\n  Block 0\n    (%s)\nin"
               % (name.capitalize(), ",\n     ".join(rows)))
    out.append("cont done ($caml%s)" % name.capitalize())
    for line in out:
        if len(line) > 79 and line.startswith("let ") and " = " in line:
            head, body = line.split(" = ", 1)
            line = head + " =\n  " + body
        print(line)

main()
