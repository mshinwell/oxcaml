#!/usr/bin/env python3
"""Generates an .fl file that checks the unary [Int_arith] with
[Swap_byte_endianness] at one integer kind against a reference written here
on Python's unbounded integers. It goes with the work of P1 on the
primitives and is not part of any build; it follows P1-int-shift.py beside
it.

Each check swaps the bytes of one number and compares the result with the
reference. The term returns a block with one field for each check, which is
1 where the two agree. Run by flsemantics, every field is 1 before Simplify
if the model agrees with the reference, and after Simplify, which folds
everything, if Simplify agrees with it.

The reference: at the two kinds of immediates, the two low bytes swapped
and nothing else; at the other kinds, the integer of the kind that has the
bytes in the opposite order.

Usage: P1-int-bswap.py KIND NAME
writes NAME.fl to standard output; KIND is one of the keys of KINDS."""
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

def bswap(kind, w, a):
    if kind in ("tagged", "imm"):
        return ((a & 0xff) << 8) | ((a >> 8) & 0xff)
    count = w // 8
    unsigned = a & ((1 << w) - 1)
    swapped = int.from_bytes(unsigned.to_bytes(count, "little"), "big")
    return wrap(w, swapped)

def main():
    kind, name = sys.argv[1], sys.argv[2]
    w, flag, suffix = KINDS[kind]
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    values = [lo, lo + 1, lo + 255, lo + 256, -(1 << 31), -(1 << 24), -65537,
              -65536, -32769, -32768, -4660, -257, -256, -255, -129, -128,
              -127, -2, -1, 0, 1, 2, 127, 128, 255, 256, 257, 4660, 32767,
              32768, 65535, 65536, 1193046, (1 << 24) - 1, 1 << 24,
              305419896, (1 << 31) - 1, 1 << 31, (1 << 32) - 1, 1 << 32,
              72623859790382856, 1 << 56, hi - 256, hi - 255, hi - 1, hi]
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
        r, c, t = fresh("r"), fresh("c"), fresh("t")
        arg, expected = operand(a), operand(bswap(kind, w, a))
        out.append("let %s = %%int_uarith.%s`bswp` (%s) in" % (r, prefix, arg))
        out.append("let %s = %%int_comp.%s`eq` (%s, %s) in"
                   % (c, prefix, r, expected))
        out.append("let %s = %%tag_imm (%s) in" % (t, c))
        results.append(t)
    symbol = "$caml" + name[0].upper() + name[1:]
    out.append("let %s = Block 0 (%s) in" % (symbol, ", ".join(results)))
    out.append("cont done (%s)" % symbol)
    print("\n".join(out))

main()
