#!/usr/bin/env python3
"""Generates an .fl file that checks [Num_conv] from one integer kind to
every integer kind against a reference written here on Python's unbounded
integers: the number wrapped to the width of the destination. It goes with
the work of P1 on the primitives and is not part of any build; it follows
C1-int-ops.py beside it.

Each check converts one number and compares the result with the reference.
The term returns a block with one field for each check, which is 1 where the
two agree. Run by flsemantics, every field is 1 before Simplify if the model
agrees with the reference, and after Simplify, which folds everything, if
Simplify agrees with it.

Usage: P1-num-conv.py SRC NAME [full | small]
writes NAME.fl to standard output; SRC is one of the keys of KINDS. The
numbers are the bounds of every kind with their neighbours (full, the
default), or one number on each side of each bound (small)."""
import sys

KINDS = {
    # name: (width, flag of %num_conv, flag of %int_comp and %int_barith,
    #        literal suffix)
    "tagged": (63, "tagged_imm", None, ""),
    "imm": (63, "imm", "imm", "i"),
    "int8": (8, "int8", "int8", "s"),
    "int16": (16, "int16", "int16", "S"),
    "int32": (32, "int32", "int32", "l"),
    "int64": (64, "int64", "int64", "L"),
    "nativeint": (64, "nativeint", "nativeint", "n"),
}

def wrap(w, z):
    return (z + (1 << (w - 1))) % (1 << w) - (1 << (w - 1))

def main():
    src, name = sys.argv[1], sys.argv[2]
    small = len(sys.argv) > 3 and sys.argv[3] == "small"
    w, _, _, _ = KINDS[src]
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    # The bounds of every kind, and their neighbours: where a conversion
    # to a narrower kind wraps.
    values = [0, -1, lo, hi] if small else [0, 1, -1, 5, -7]
    for width in (8, 16, 32, 63, 64):
        least, greatest = -(1 << (width - 1)), (1 << (width - 1)) - 1
        if small:
            values += [least - 1, greatest + 1]
        else:
            for edge in (least, greatest, (1 << width) - 1):
                values += [edge - 1, edge, edge + 1]
    values = sorted(set(v for v in values if lo <= v <= hi))
    out = []
    counter = [0]
    def fresh(base):
        counter[0] += 1
        return "%s%d" % (base, counter[0])
    # A literal has to fit OCaml's [int] whatever its kind, so the numbers
    # beyond 63 bits are computed, by a multiplication that does not wrap.
    names = {}
    def operand(kind, v):
        _, _, flag, suffix = KINDS[kind]
        prefix = "" if flag is None else "`%s`." % flag
        def literal(v):
            return "%d%s" % (v, suffix)
        if -(1 << 62) <= v <= (1 << 62) - 1:
            return literal(v)
        if (kind, v) not in names:
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
            names[(kind, v)] = x
        return names[(kind, v)]
    results = []
    for dst in KINDS:
        dw, dflag, dcomp, _ = KINDS[dst]
        prefix = "" if dcomp is None else "`%s`." % dcomp
        for v in values:
            r, c, t = fresh("r"), fresh("c"), fresh("t")
            arg = operand(src, v)
            expected = operand(dst, wrap(dw, v))
            out.append("let %s = %%num_conv.[`%s`].[`%s`] (%s) in"
                       % (r, KINDS[src][1], dflag, arg))
            out.append("let %s = %%int_comp.%s`eq` (%s, %s) in"
                       % (c, prefix, r, expected))
            out.append("let %s = %%tag_imm (%s) in" % (t, c))
            results.append(t)
    symbol = "$caml" + name[0].upper() + name[1:]
    out.append("let %s = Block 0 (%s) in" % (symbol, ", ".join(results)))
    out.append("cont done (%s)" % symbol)
    print("\n".join(out))

main()
