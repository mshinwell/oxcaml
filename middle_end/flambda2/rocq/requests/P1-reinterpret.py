#!/usr/bin/env python3
"""Generates an .fl file that checks [Reinterpret_64_bit_word] between a
tagged immediate and an int64, in one direction, against a reference written
here on Python's unbounded integers. It goes with the work of P1 on the
primitives and is not part of any build; it follows P1-int-bswap.py beside
it.

Each check reinterprets one number and compares the result with the
reference. The term returns a block with one field for each check, which is
1 where the two agree. Run by flsemantics, every field is 1 before Simplify
if the model agrees with the reference, and after Simplify, which folds
everything, if Simplify agrees with it.

The reference: the machine word of the tagged immediate i is 2 * i + 1; the
tagged immediate of an int64 is the int64 with its lowest bit set, read as
such a word, which is the int64 halved towards minus infinity.

Usage: P1-reinterpret.py DIRECTION NAME
writes NAME.fl to standard output; DIRECTION is int63_as_int64 or
int64_as_int63."""
import sys

def main():
    direction, name = sys.argv[1], sys.argv[2]
    if direction == "int63_as_int64":
        w, suffix, flag = 63, "", None
        out_suffix, out_flag = "L", "int64"
        f = lambda i: 2 * i + 1
    else:
        w, suffix, flag = 64, "L", "int64"
        out_suffix, out_flag = "", None
        f = lambda word: (word | 1) >> 1
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    values = [lo, lo + 1, lo + 2, lo + 3, -(1 << 62) - 1, -(1 << 62),
              -(1 << 62) + 1, -(1 << 32), -65536, -257, -4, -3, -2, -1, 0, 1,
              2, 3, 4, 5, 255, 256, 65535, 1 << 32, (1 << 62) - 2,
              (1 << 62) - 1, 1 << 62, (1 << 62) + 1, hi - 3, hi - 2, hi - 1,
              hi]
    values = sorted(set(v for v in values if lo <= v <= hi))
    out = []
    counter = [0]
    def fresh(base):
        counter[0] += 1
        return "%s%d" % (base, counter[0])
    # A literal has to fit OCaml's [int] whatever its kind, so the numbers
    # beyond 63 bits are computed, by a multiplication that does not wrap.
    names = {}
    def operand(v, suffix, flag):
        prefix = "" if flag is None else "`%s`." % flag
        def literal(v):
            return "%d%s" % (v, suffix)
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
    out_prefix = "" if out_flag is None else "`%s`." % out_flag
    results = []
    for a in values:
        r, c, t = fresh("r"), fresh("c"), fresh("t")
        arg = operand(a, suffix, flag)
        expected = operand(f(a), out_suffix, out_flag)
        out.append("let %s = %%reinterpret_64_bit_word.%s (%s) in"
                   % (r, direction, arg))
        out.append("let %s = %%int_comp.%s`eq` (%s, %s) in"
                   % (c, out_prefix, r, expected))
        out.append("let %s = %%tag_imm (%s) in" % (t, c))
        results.append(t)
    symbol = "$caml" + name[0].upper() + name[1:]
    out.append("let %s = Block 0 (%s) in" % (symbol, ", ".join(results)))
    out.append("cont done (%s)" % symbol)
    print("\n".join(out))

main()
