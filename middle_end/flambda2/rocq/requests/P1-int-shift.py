#!/usr/bin/env python3
"""Generates an .fl file that checks [Int_shift] at one integer kind against
a reference written here on Python's unbounded integers. It goes with the
work of P1 on the primitives and is not part of any build; it follows
C1-int-ops.py beside it.

Each check shifts one number by one amount and compares the result with the
reference. The term returns a block with one field for each check, which is
1 where the two agree. Run by flsemantics, every field is 1 before Simplify
if the model agrees with the reference, and after Simplify, which folds
everything, if Simplify agrees with it.

The amounts are those on which the model gives the shift a value: from 0 up
to, and not including, the bound of the kind, which is its width, and 64
for the tagged immediates.

Usage: P1-int-shift.py KIND NAME [full | small]
writes NAME.fl to standard output; KIND is one of the keys of KINDS."""
import sys

KINDS = {
    # name: (width, bound of the amounts, flag, literal suffix)
    "tagged": (63, 64, None, ""),
    "imm": (63, 63, "imm", "i"),
    "int8": (8, 8, "int8", "s"),
    "int16": (16, 16, "int16", "S"),
    "int32": (32, 32, "int32", "l"),
    "int64": (64, 64, "int64", "L"),
    "nativeint": (64, 64, "nativeint", "n"),
}

def wrap(w, z):
    return (z + (1 << (w - 1))) % (1 << w) - (1 << (w - 1))

def unsigned(w, z):
    return z + (1 << w) if z < 0 else z

SHIFTS = {
    "lsl": lambda w, a, s: wrap(w, a << s),
    "lsr": lambda w, a, s: wrap(w, unsigned(w, a) >> s),
    "asr": lambda w, a, s: a >> s,
}

def main():
    kind, name = sys.argv[1], sys.argv[2]
    small = len(sys.argv) > 3 and sys.argv[3] == "small"
    w, bound, flag, suffix = KINDS[kind]
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    if small:
        values = [lo, -7, -1, 0, 1, 13, hi]
        amounts = [0, 1, w // 2, w - 1, bound - 1]
    else:
        values = [lo, lo + 1, -100, -7, -2, -1, 0, 1, 2, 3, 13, 100, hi - 1,
                  hi]
        amounts = [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 61, 62, 63, w - 2,
                   w - 1, bound - 1]
    values = sorted(set(v for v in values if lo <= v <= hi))
    amounts = sorted(set(s for s in amounts if 0 <= s < bound))
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
            if v % 2 == 0:
                out.append("let %s = %%int_barith.%s`mul` (%s, %s) in"
                           % (x, prefix, literal(v // 2), literal(2)))
            else:
                # v = 2 * (v // 2) + 1, computed without wrapping
                half = fresh("half")
                out.append("let %s = %%int_barith.%s`mul` (%s, %s) in"
                           % (half, prefix, literal(v // 2), literal(2)))
                out.append("let %s = %%int_barith.%s`add` (%s, %s) in"
                           % (x, prefix, half, literal(1)))
            names[v] = x
        return names[v]
    results = []
    for a in values:
        for s in amounts:
            for op, f in SHIFTS.items():
                r, c, t = fresh("r"), fresh("c"), fresh("t")
                arg, expected = operand(a), operand(f(w, a, s))
                out.append("let %s = %%int_shift.%s`%s` (%s, %di) in"
                           % (r, prefix, op, arg, s))
                out.append("let %s = %%int_comp.%s`eq` (%s, %s) in"
                           % (c, prefix, r, expected))
                out.append("let %s = %%tag_imm (%s) in" % (t, c))
                results.append(t)
    symbol = "$caml" + name[0].upper() + name[1:]
    out.append("let %s = Block 0 (%s) in" % (symbol, ", ".join(results)))
    out.append("cont done (%s)" % symbol)
    print("\n".join(out))

main()
