#!/usr/bin/env python3
#******************************************************************************
#*                                  OxCaml                                    *
#* -------------------------------------------------------------------------- *
#*                               MIT License                                  *
#*                                                                            *
#* Copyright (c) 2026 Jane Street Group LLC                                   *
#* opensource-contacts@janestreet.com                                         *
#*                                                                            *
#* Permission is hereby granted, free of charge, to any person obtaining a    *
#* copy of this software and associated documentation files (the "Software"), *
#* to deal in the Software without restriction, including without limitation  *
#* the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
#* and/or sell copies of the Software, and to permit persons to whom the      *
#* Software is furnished to do so, subject to the following conditions:       *
#*                                                                            *
#* The above copyright notice and this permission notice shall be included    *
#* in all copies or substantial portions of the Software.                     *
#*                                                                            *
#* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
#* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
#* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
#* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
#* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
#* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
#* DEALINGS IN THE SOFTWARE.                                                  *
#******************************************************************************



"""names.py FILE.v ... : THE NAMES THAT THE REALISATIONS WRITE WITHOUT A
MODULE, and the modules of a file that are named like a unit (GUIDE.md,
section 7). The Makefile's target names, after the extracted files are
made. names.py --self-test tries the reading of OCaml on made-up texts. It
follows no file of the compiler.

The kit and decl/ give a Rocq name its OCaml text ([Extract Inlined Constant
negb => "not".]), and Rocq's extraction writes that text at each use. For
some names the text is ONE NAME WITHOUT A MODULE: [not], [max], [compare],
[ref], [fst], [incr] (Rocq's [negb], [Z.max], [poly_compare], [mk_ref],
[fst], [Stdlib_.incr]). OCaml reads such a name where it stands: if the
extracted file has, around the use, its own binding of that name (a
variable [max], a function [compare] of a module of the file), the use is
of that binding and not of the standard library's value, and OCaml says
nothing when the types agree. Rocq does not see it: there the two names
differ. The other texts are paths ([Lazy.force], [Flambda.Expr.descr]), and
OCaml reads the first name of a path where it stands, too: in a file that
defines a module of that name, the path is read in that module.

THE TABLE is read from the texts themselves, at each run: every [Extract
Inlined Constant R => "N".] and [Extract Constant R => "N".] of
monad/id/Port_monad.v and of the files of decl/ whose text N is one name
that begins with a small letter or [_] and is no word of OCaml. R is the
Rocq name as a ported file writes it: as the directive has it for the kit
([Z.max], [negb]), and with the modules of its file for decl/
([Stdlib_.incr]). R IS A TYPE if its file has [Parameter R : Type] or
[Definition R : Type] ([int], [exn], [Stdlib_.char]).

1. A NAME WITHOUT A MODULE. For each FILE.v and its extracted file F:

  if the OCaml text of F MAY BIND N, then FILE.v does not use R.

(So a file may have a variable [max], as the compiler's file has: it then
has no [Z.max].) Both sides are read AS WORDS.

- FILE.v USES R: outside comments and strings, the name R stands as it is
  written above, with no letter, figure, quote or dot directly before or
  after it. For a name of decl/ the last name alone counts too ([incr]) if
  a sentence of FILE.v with [Import] names the module ([Stdlib_]).
- F MAY BIND N, for a value: outside comments and strings, the word N,
  with no dot or [#] directly before it, stands
  . after [~] or [?] (a label);
  . after [as], [val] or [external];
  . where a pattern may stand: after [let] or [and] up to the [=] outside
    brackets; after [for] up to [=]; after [fun] up to [->]; after
    [function], [with] or [|] up to [->] or [when]. A word of OCaml that
    no pattern has ([let], [in], [if], [match], [type], [module], ..) ends
    such a place. Inside such a place, what follows a colon (the type of
    a parameter) up to the bracket that closes, or to the end of the
    place, is not counted.
  This is MORE than OCaml binds: a field of a record pattern ([{ max = x
  }]), a field in [{ t with max = e }], the default of an optional
  parameter, a [val] of a signature. It can only make the check refuse a
  file that is right.
- F MAY BIND N, for a type: N stands directly after [type] or [nonrec], or
  directly before the [=] of a type definition (after [type] and before
  the next item, outside the brackets of the definition).
- THE FILES OF THE FOLDER THAT F OPENS are read in the same way, and what
  they may bind counts as bound in F: runtime/port_monad.ml and
  runtime/port_abbreviations.ml where F has [open Port_monad] and [open
  Port_abbreviations], and extracted/simplify_import.ml where F has [open
  Simplify_import] or [open! Simplify_import].

2. A MODULE OF THE FILE NAMED LIKE A UNIT. THE FIRST NAMES are the first
names of the paths of all the texts of the kit and of decl/ (every
[Extract] directive, also those of types and of constructors; not the
files decl/X__local.v, which declare the modules that the file X makes for
itself: their first names are those modules). F DEFINES A MODULE U, as
words, by [module U] (not [module type U]) or [module rec U]. For each
module U of F that is a first name, ONE of these must hold:

  a. FILE.v, or abbrev/FILE/Port_abbreviations.v, has a sentence [Module
     U] ([Module U.] or [Module U := P.]). Then Rocq reads [U.x] in the
     file's module too: the name that the ported file writes is of that
     module, and its text is that module's. THE WHOLE PATH [decl.U.x]
     still reaches the unit's own declaration in Rocq, and OCaml would
     read its text [U.x] in the file's module. FILE.v may have the words
     [decl.U.] only
     . between [Module U.] and [End U.]: in OCaml the name of a module is
       not in sight inside its own definition ([module U = struct .. end]
       without [rec]), so the path is the unit's there;
     . before a constructor ([decl.U.C], C with a capital and no dot after
       it). OCaml reads its text in the file's module. THE TOOL DOES NOT
       CHECK that the constructor of that module is the unit's: a module
       of the file could define a type and a constructor of the same
       names, the type that the text writes beside the constructor would
       be read in that module too, and OCaml's check of the types would
       pass. THE USES OF TODAY WERE READ, thirteen: all are
       [decl.Function_declarations.Code_id] and [.Deleted], in three
       files that open Simplify_import (Simplify_apply_expr.v, 1;
       Simplify_set_of_closures.v, 8; Simplify_set_of_closures_context.v,
       4). The module in sight there is [module Function_declarations =
       Flambda.Function_declarations] (extracted/simplify_import.ml, as
       the compiler's file has it), and the compiler's Flambda has
       [module Function_declarations = Function_declarations]
       (middle_end/flambda2/terms/flambda.mli and flambda.ml): two other
       names of the unit itself, so the constructor is the unit's. A new
       use needs the same reading; the last line of the tool counts them.
  b. the module is [module U = struct include U ..]. THIS IS A TEST OF
     FOUR WORDS: after the name the tool finds [=], [struct], [include]
     and U, and reads no further. It does NOT check what follows the
     [include]: a definition there of a name that the unit has ([let rev
     ..] in a [module List]) would replace the unit's for the rest of the
     file, a path to it would be read as the new one, and the tool would
     say nothing. THE MODULES OF TODAY WERE READ, three, all in
     extracted/simplify_binary_primitive.ml. Target_ocaml_int adds one
     module, [Set_], a name that the unit does not have. Numeric_types
     adds a module type [Float_by_bit_pattern_] and defines again two
     modules of the unit ([Float_by_bit_pattern],
     [Float32_by_bit_pattern]). Number_adjuncts defines again two module
     types of the unit ([Num_common], which includes the unit's and adds
     [Set_]; [Int_number_kind], the unit's text read with that
     [Num_common]) and seven of its modules ([For_tagged_immediates] ..
     [For_nativeints]). Each module that is defined again is [struct
     include M ..] of the unit's module M of the same name, and what
     follows the [include] is a new module [Set_], or a module of M
     ([Num], [Pair]) defined again in the same way. Outside the
     signatures of the module types, the three have no [let], [type],
     [exception], [external] or [open]: no value, type or constructor of
     the unit is defined again, and a path through U to one reaches the
     unit's. A new module of this form needs the same reading; the last
     line of the tool counts them.
  c. the module is inside another module of F, and from its definition to
     the [end] of that module the word U is nowhere followed by a dot:
     where the name is in sight, no path begins with it.

The modules of the folder's files that F opens: runtime/port_monad.ml and
runtime/port_abbreviations.ml define no module that is a first name;
extracted/simplify_import.ml defines one only if decl/Simplify_import.v,
which the ported files import, has [Module U] too, and then the rule of
the whole path (a) holds for it in each file that opens Simplify_import.

WHAT IT DOES NOT ESTABLISH.
- The scopes: rule 1 is by file. A file that binds [max] and uses [Z.max]
  in another function is refused, though OCaml would read it rightly. In
  rule 2, a and b do not look where the module is: a module of FILE.v at
  any depth answers a module of F at any depth.
- What a module of 2b defines after its [include]: the test is of the
  four words after its name (above).
- That a constructor written with the whole path (2a) is the unit's: the
  tool does not look at the module of the file that OCaml reads it in,
  and OCaml's check of the types does not tell a type and a constructor
  of the same names in that module from the unit's (above).
- That the module of Rocq and the module of OCaml in 2a are the same one:
  [Module Int32 := Numeric_types.Int32.] beside [module Int32 =
  Numeric_types.Int32] are two lines that the tool does not compare.
- What the modules of the compiler bring that the file opens or includes
  ([open! Flambda.Import], [open! Flambda], an [include] of the result
  of a functor or of a parameter of a functor): they are not of this
  folder and are not read. The last line of the tool names them (not a
  module that the file itself defines: its text is read with the file).
  Inside a module of the file, after such an [include], a bare name may
  be one that the [include] brought. The
  compiler's own file has the same lines at its head, so a name that the
  compiler writes bare is read through the same modules in both. A text of
  decl/ is a whole path from a unit where the compiler may write a short
  one: if such a module had a module of the unit's name inside it, the
  path would be read there. OCaml's check of the types (tools/check.sh) is
  the only guard for it.
- A name that a ported file reaches under another name than R: through a
  notation, or through an abbreviation of a module of decl/ ([Module S :=
  Stdlib_.] and then [S.incr]). No ported file has one for these names.
- The texts that are not one name and no path: an operator ([(+)], [(=)],
  [!], [(:=)], [(||)]) is read where it stands as well, and a file or a
  module that it opens could define one. The tool does not look. (No
  extracted file defines an operator; the folder's two runtime files
  define none.)
- The words of OCaml in a text ([assert]), the numbers, and the texts that
  are functions ([(fun x__1 -> ..)]): their paths are read for rule 2,
  their parameters [x__N] and [f__N] are not looked at.
- A parameter of a functor ([module F (U : S) = ..]) is not counted as a
  module that F defines.
The tool reads the extracted file as ocamlformat leaves it.
"""
import collections
import os
import re
import sys

sys.dont_write_bytecode = True
import papp

KEYWORDS = set(
    """and as assert begin class constraint do done downto else end exception
    external false for fun function functor if in include inherit initializer
    lazy let match method module mutable new nonrec object of open or private
    rec sig struct then to true try type val virtual when while with""".split()
)
# The words of OCaml that stand in no pattern: one ends a place where a
# pattern may stand.
ENDS = set(
    """and begin class do done else end exception external for fun function
    functor if in include let match module open sig struct then to try type
    val when while with""".split()
)
# Those that end a type definition (not [and]: it goes on with another type).
ITEMS = set(
    """class end exception external include let module open sig struct
    val""".split()
)
# Those that an [end] closes.
BLOCKS = ("struct", "sig", "begin", "object")

OTOKEN = re.compile(
    r"""
      "[^"]*"                                # a string (its inside is x)
    | '(?:\\[^']*|[^\\'])'                   # a character
    | (?P<label>[~?])?(?P<word>[a-z_][A-Za-z0-9_']*)
    | (?P<upper>[A-Z][A-Za-z0-9_']*)
    | \[\| | \|\] | -> | :: | := | :> | ;; | \|\|
    | [=|(){}\[\];:,.\#]
    """,
    re.X,
)

DIRECTIVE = re.compile(
    r'Extract\s+(?:Inlined\s+)?Constant\s+(%s)(?:\s+"[^"]*")*\s*=>\s*"((?:[^"]|"")*)"\s*$' % papp.PPATH
)
ANY_TEXT = re.compile(r'"((?:[^"]|"")*)"')
ONE_NAME = re.compile(r"[a-z_][A-Za-z0-9_']*")
HEAD = re.compile(r"(?<![A-Za-z0-9_'.])([A-Z][A-Za-z0-9_']*)\.")

Bound = collections.namedtuple("Bound", "values types modules opened")
# A module that the text defines: its line, whether it is [= struct include
# U], whether it is inside another module, and whether the word U is
# followed by a dot between its definition and the [end] of that module.
Module = collections.namedtuple("Module", "line extends inside path_after")


def read_table():
    """(R -> (N, whether R is a type) for the texts that are one name; the
    first names of the paths of all the texts -> where one is). R is the
    name as a ported file writes it."""
    bare = {}
    heads = {}
    kit = os.path.join(papp.PORT, "monad", "id", "Port_monad.v")
    files = [(kit, None)] + [
        (os.path.join(papp.DECL, name), name[:-2])
        for name in sorted(os.listdir(papp.DECL))
        if name.endswith(".v")
    ]
    for path, module in files:
        raw = open(path).read()
        text = papp.blank(raw, False)
        stack = [module] if module else []
        local = bool(module) and module.endswith("__local")
        for a, b in papp.sentences(text):
            m = papp.STRUCTURE.match(text, a, b)
            if m and m.group(1) != "Section" and module:
                if m.group(1) == "End":
                    if len(stack) > 1 and stack[-1] == m.group(2):
                        stack.pop()
                elif ":=" not in text[m.end():b]:
                    stack.append(m.group(2))
                continue
            if not text.startswith("Extract", a):
                continue
            # the texts stand in the file as it is (the strings are blank
            # in [text])
            sentence = raw[a:b]
            where = "%s:%d" % (os.path.relpath(path, papp.PORT), raw.count("\n", 0, a) + 1)
            if not local:
                for s in ANY_TEXT.findall(sentence):
                    for u in HEAD.findall(papp.blank_ocaml(s.replace('""', '"'))):
                        heads.setdefault(u, where)
            d = DIRECTIVE.match(sentence)
            if d and ONE_NAME.fullmatch(d.group(2)) and d.group(2) not in KEYWORDS:
                is_type = bool(
                    re.search(
                        r"(?<![A-Za-z_0-9'.])(?:Parameter|Definition)\s+%s\s*:\s*Type(?![A-Za-z_0-9'])"
                        % re.escape(d.group(1)),
                        text,
                    )
                )
                bare[".".join(stack + [d.group(1)])] = (d.group(2), is_type)
    return bare, heads


def may_bind(raw):
    """What OCaml text may bind: the names of values and of types, each
    with its lines; the modules that it defines; the modules that it opens
    or includes, as written. The text is read with its comments and the
    inside of its strings blank, sign for sign; the number of a line is
    counted in the text as it is (a string that goes on after a backslash
    at the end of a line has no line break there once it is blank)."""
    text = papp.blank_ocaml(raw)
    if len(text) != len(raw):
        raise ValueError("the blank text has not the length of the text")
    tokens = [m for m in OTOKEN.finditer(text)]
    values = collections.defaultdict(list)
    types = collections.defaultdict(list)
    modules = collections.defaultdict(list)
    opened = []
    regions = []  # (the token that ends it, the depth where it began)
    depth = 0
    annotation = None  # the depth at which the type of a parameter began
    in_type = None  # the depth of a type definition that is being read
    after = None  # the word before: as, val, external, type, nonrec
    blocks = []  # the words that an [end] closes, with whether a module
    defined = []  # (the name, the token, the number of blocks around it)

    def line(m):
        return raw.count("\n", 0, m.start()) + 1

    def token(k):
        return tokens[k].group(0) if 0 <= k < len(tokens) else ""

    for k, m in enumerate(tokens):
        t = m.group(0)
        word = m.group("word")
        before = token(k - 1)
        following = token(k + 1)
        if t in ("(", "[", "{", "[|"):
            depth += 1
            after = None
            continue
        if t in (")", "]", "}", "|]"):
            depth -= 1
            regions = [r for r in regions if r[1] <= depth]
            if annotation is not None and depth < annotation:
                annotation = None
            if in_type is not None and depth < in_type:
                in_type = None
            after = None
            continue
        if m.group("upper"):
            if before == "module" or (before == "rec" and token(k - 2) == "module"):
                defined.append((t, k, len(blocks)))
            elif before in ("open", "include"):
                # ([open!] too: the sign [!] is no token here)
                opened.append(text[m.start():text.find("\n", m.start())].split()[0].rstrip(";"))
            after = None
            continue
        if word and not m.group("label") and word in KEYWORDS:
            if word in BLOCKS:
                blocks.append(word)
            elif word == "end" and blocks:
                blocks.pop()
            if word in ENDS:
                regions = [r for r in regions if r[1] < depth]
                annotation = None
            if word in ITEMS and in_type is not None and depth <= in_type:
                in_type = None
            named = before in ("module", ":", "(")
            if word == "type" and not named:
                # (not [module type], and not a type that a function names
                # for itself: [fun (type a) ..], [let f : type a. ..])
                in_type = depth
            elif word in ("let", "for") or (word == "and" and in_type is None):
                regions.append(("=", depth))
            elif word in ("fun", "function", "with"):
                regions.append(("->", depth))
            after = word if word in ("as", "val", "external", "type", "nonrec") else None
            if word == "type" and named:
                after = None
            continue
        if word:
            if before in (".", "#"):
                after = None
                continue
            if in_type is not None:
                if after in ("type", "nonrec") or (following == "=" and depth == in_type):
                    types[word].append(line(m))
            elif (
                m.group("label")
                or after in ("as", "val", "external")
                or (regions and annotation is None)
            ):
                values[word].append(line(m))
            after = None
            continue
        # the signs
        if t == "|" and in_type is None:
            regions = [r for r in regions if r != ("->", depth)]
            regions.append(("->", depth))
        elif t in ("=", "->"):
            if (t, depth) in regions:
                regions = [r for r in regions if r != (t, depth)]
                if annotation is not None and annotation <= depth:
                    annotation = None
        elif (
            t == ":"
            and regions
            and annotation is None
            and in_type is None
            and not tokens[k - 1].group("label")
        ):
            # (not the colon of a label: [~f:x] binds x)
            annotation = depth
        if t not in (".", "#"):
            after = None
    # each module: is it an extension of the unit of its name; and, if it
    # is inside another module, is its name followed by a dot before the
    # [end] of that module
    for name, k, around in defined:
        extends = [token(k + i) for i in (1, 2, 3, 4)] == ["=", "struct", "include", name]
        path_after = False
        if around:
            level = around
            for j in range(k + 1, len(tokens)):
                w = token(j)
                if w in BLOCKS:
                    level += 1
                elif w == "end":
                    level -= 1
                    if level < around:
                        break
                elif w == name and token(j + 1) == ".":
                    path_after = True
                    break
        modules[name].append(Module(line(tokens[k]), extends, bool(around), path_after))
    return Bound(values, types, modules, opened)


def uses(text, imported, rocq):
    """The line where the Rocq text (comments and strings blank) uses the
    name; None if it does not."""
    forms = [rocq]
    if "." in rocq and rocq.split(".")[0] in imported:
        forms.append(rocq.split(".", 1)[1])
    for f in forms:
        m = re.search(r"(?<![A-Za-z_0-9'.])%s(?![A-Za-z_0-9'.])" % re.escape(f), text)
        if m:
            return text.count("\n", 0, m.start()) + 1
    return None


def rocq_modules(path):
    """The names of the modules that a Rocq file has a sentence [Module U]
    for; the empty set if the file is not there."""
    try:
        text = papp.blank(open(path).read(), False)
    except IOError:
        return set()
    out = set()
    for a, b in papp.sentences(text):
        m = papp.STRUCTURE.match(text, a, b)
        if m and m.group(1) == "Module":
            out.add(m.group(2))
    return out


def module_spans(text, u):
    """Where the Rocq text has [Module u.] .. [End u.]: (the start of the
    first sentence, the full stop of the last)."""
    out = []
    begun = []
    for a, b in papp.sentences(text):
        m = papp.STRUCTURE.match(text, a, b)
        if not m or m.group(2) != u:
            continue
        if m.group(1) == "Module" and ":=" not in text[m.end():b]:
            begun.append(a)
        elif m.group(1) == "End" and begun:
            out.append((begun.pop(), b))
    return out


def shown(lines):
    return ", ".join(str(n) for n in lines[:4]) + (" .." if len(lines) > 4 else "")


FOLDER = {
    "Port_monad": "runtime/port_monad.ml",
    "Port_abbreviations": "runtime/port_abbreviations.ml",
    "Simplify_import": "extracted/simplify_import.ml",
}


def main(files):
    bare, heads = read_table()
    bad = 0
    # the files of the folder that an extracted file opens, and their
    # modules that are first names
    folder = {}
    for unit, rel in sorted(FOLDER.items()):
        try:
            folder[unit] = may_bind(open(os.path.join(papp.PORT, rel)).read())
        except IOError:
            print("names: %s is not there" % rel)
            bad += 1
            continue
        mirror = (
            rocq_modules(os.path.join(papp.DECL, "Simplify_import.v"))
            if unit == "Simplify_import"
            else set()
        )
        for u in sorted(set(folder[unit].modules) & set(heads)):
            if u in mirror:
                continue
            print(
                "%s defines a module %s (line %s), and a text of the kit or of decl/ (%s) is a "
                "path that begins with %s: in a file that opens %s, OCaml would read the path "
                "in that module%s"
                % (
                    rel,
                    u,
                    shown([d.line for d in folder[unit].modules[u]]),
                    heads[u],
                    u,
                    unit,
                    " (decl/Simplify_import.v has no [Module %s])" % u if unit == "Simplify_import" else "",
                )
            )
            bad += 1
    outside = collections.Counter()
    pairs = 0
    answered = collections.Counter()
    whole_paths = collections.Counter()
    for path in files:
        raw = open(path).read()
        text = papp.without_labels(papp.blank(raw, False))
        imported = set()
        for a, b in papp.sentences(text):
            if re.search(r"(?<![A-Za-z_0-9'.])Import(?![A-Za-z_0-9'])", text[a:b]):
                imported.update(re.findall(papp.PNAME, text[a:b]))
        where, ml = papp.extracted_of(path)
        if ml is None:
            print("%s: %s is not there" % (path, where))
            bad += 1
            continue
        own = may_bind(ml)
        sources = [(where, own)]
        for o in own.opened:
            if o in folder:
                sources.append((FOLDER[o], folder[o]))
            elif o not in FOLDER and o.split(".")[0] not in own.modules:
                # (a module that the file itself defines is read with the
                # file)
                outside[o] += 1
        # 1. a name without a module
        for rocq, (ocaml, is_type) in sorted(bare.items()):
            used = uses(text, imported, rocq)
            if used is None:
                continue
            pairs += 1
            for source, bound in sources:
                lines = (bound.types if is_type else bound.values).get(ocaml)
                if lines:
                    print(
                        "%s:%d: %s is printed as the bare name %s, and %s may bind %s%s (line %s): "
                        "in OCaml the use could be of that binding"
                        % (path, used, rocq, ocaml, source, "the type " if is_type else "", ocaml, shown(lines))
                    )
                    bad += 1
        # 2. a module of the file named like a unit
        rel = os.path.relpath(os.path.abspath(path), os.path.abspath(papp.PORT))
        library = os.path.join(papp.ABBREV, os.path.basename(rel)[:-2].lower(), "Port_abbreviations.v")
        mirror = rocq_modules(path) | rocq_modules(library)
        # the modules in sight that Rocq has too: U -> where OCaml has it
        in_sight = {}
        for source, bound in sources[1:]:
            for u in sorted(set(bound.modules) & set(heads)):
                in_sight.setdefault(u, source)
        for u in sorted(set(own.modules) & set(heads)):
            for d in own.modules[u]:
                here = "%s: %s defines a module %s (line %d), and a text of the kit or of decl/ (%s) is a path that begins with %s" % (
                    path,
                    where,
                    u,
                    d.line,
                    heads[u],
                    u,
                )
                if u in mirror:
                    in_sight.setdefault(u, where)
                    answered["a"] += 1
                elif d.extends:
                    answered["b"] += 1
                elif d.inside and not d.path_after:
                    answered["c"] += 1
                else:
                    print(
                        "%s: in this file OCaml would read the path in that module (the ported "
                        "file has no [Module %s], the module is not [= struct include %s], and %s)"
                        % (
                            here,
                            u,
                            u,
                            "its name is followed by a dot before the [end] of the module around it"
                            if d.inside
                            else "it is inside no other module",
                        )
                    )
                    bad += 1
        # the whole path of the unit's declarations, where a module of the
        # name is in sight
        for u, source in sorted(in_sight.items()):
            spans = module_spans(text, u)
            for m in re.finditer(r"(?<![A-Za-z_0-9'])decl\.%s\.(%s)(\.?)" % (re.escape(u), papp.PNAME), text):
                if any(a <= m.start() < b for a, b in spans):
                    continue
                if m.group(1)[0].isupper() and not m.group(2):
                    whole_paths["a constructor"] += 1
                    continue
                print(
                    "%s:%d: the whole path [decl.%s.%s] is of the unit %s, and %s defines a module "
                    "%s: OCaml would read its text in that module (it is not between [Module %s.] "
                    "and [End %s.], and it is no constructor)"
                    % (path, text.count("\n", 0, m.start()) + 1, u, m.group(1), u, source, u, u, u)
                )
                bad += 1
            whole_paths["inside the module"] += sum(
                1
                for m in re.finditer(r"(?<![A-Za-z_0-9'])decl\.%s\." % re.escape(u), text)
                if any(a <= m.start() < b for a, b in spans)
            )
    if not bad:
        print(
            "names: %d files; %d names that a text of the kit or of decl/ writes without a module "
            "(%d of them types), and %d uses of one by a file (a name counted once for a file): no "
            "extracted file, and no file of the folder that it opens, may bind the name of a use. "
            "%d first names of paths: %d modules of extracted files have such a name; the ported "
            "file has a module of the name too for %d, %d are [= struct include U], %d are inside "
            "another module where no path begins with the name. The whole path [decl.U.] of a "
            "unit whose name such a module has: %d inside the module itself, %d before a "
            "constructor, none elsewhere. Not read: what the compiler's "
            "modules bring that the files open or include (%s)"
            % (
                len(files),
                len(bare),
                sum(1 for v in bare.values() if v[1]),
                pairs,
                len(heads),
                sum(answered.values()),
                answered["a"],
                answered["b"],
                answered["c"],
                whole_paths["inside the module"],
                whole_paths["a constructor"],
                ", ".join("%s in %d" % (o, n) for o, n in sorted(outside.items())) or "none",
            )
        )
    return 1 if bad else 0


def self_test():
    """The reading of OCaml on made-up texts: (what is tried, the text,
    the values that it may bind among the names asked, the types, the
    modules with how each is answered)."""
    asked = ("max", "compare", "not", "ref", "int", "incr")
    cases = [
        ("a use is no binding", "let f a b = max a b + compare a b\n", [], [], {}),
        ("a variable", "let f a =\n  let max, _ = g a in\n  max + 1\n", ["max"], [], {}),
        ("a parameter", "let f n compare = compare n n\n", ["compare"], [], {}),
        ("a function of the file", "let compare t1 t2 = 0\n", ["compare"], [], {}),
        ("and", "let rec f x = x\n\nand max a b = a\n", ["max"], [], {}),
        ("fun", "let f = List.map (fun max -> max + 1)\n", ["max"], [], {}),
        ("a case", "let f = function\n  | Some max -> max\n  | None -> 0\n", ["max"], [], {}),
        ("a case after with", "let f x = match x with Some compare -> compare | None -> 0\n", ["compare"], [], {}),
        ("as", "let f = function (_, _) as max -> max\n", ["max"], [], {}),
        ("a label", "let f ~max x = x\n", ["max"], [], {}),
        ("the variable of a label", "let f ~bound:max x = x\n", ["max"], [], {}),
        ("an optional parameter", "let f ?(max = 3) x = x\n", ["max"], [], {}),
        ("for", "let f () = for max = 0 to 3 do g max done\n", ["max"], [], {}),
        ("a guard is no pattern", "let f = function x when max x 0 = 0 -> x | x -> x\n", [], [], {}),
        ("the body of a case is no pattern", "let f = function A -> max 1 2 | B -> compare 1 2\n", [], [], {}),
        ("the type of a parameter is not counted", "let f (r : int ref) (x : int) : int ref = r\n", [], [], {}),
        ("after the type of a parameter", "let f (r : int ref) max = r\n", ["max"], [], {}),
        ("a field that is read", "let f r = r.max + M.compare 1 2\n", [], [], {}),
        ("a field of a record pattern counts", "let f { max = x; _ } = x\n", ["max"], [], {}),
        ("an array is no case", "let f a b = [| max a b |]\n", [], [], {}),
        ("a string and a comment", 'let f = "let max = 1" (* let compare = 2 *)\n', [], [], {}),
        ("val and external", "module type S = sig\n  val compare : t -> t -> int\nend\n\nexternal incr : int ref -> unit = \"%incr\"\n", ["compare", "incr"], [], {}),
        ("a type is no value", "type ref = A | B of int\n\nlet f x = x\n", [], ["ref"], {}),
        ("a type with a parameter, and the second of two", "type 'a t = 'a list\n\nand int = A\n", [], ["int"], {}),
        ("a field of a record type is nothing", "type t = { max : int; compare : int ref }\n", [], [], {}),
        ("a constructor of a variant type is no case", "type t = A | B of int ref\n\nlet f x = max x 1\n", [], [], {}),
        ("a type that a function names", "let f (type a) (x : a) max = x\n", ["max"], [], {}),
        ("a module of the file", "module List = ListLabels\n", [], [], {"List": "top, no path"}),
        ("an extension of the unit", "module Int32 = struct\n  include Int32\n\n  let zero = 0\nend\n", [], [], {"Int32": "extends"}),
        ("inside another module, no path", "module A = struct\n  module List = struct\n    let f x = x\n  end\nend\n\nlet g = List.map\n", [], [], {"A": "top, no path", "List": "inside, no path"}),
        ("inside another module, a path", "module A = struct\n  module List = struct\n    let f x = x\n  end\n\n  let g = List.f\nend\n", [], [], {"A": "top, no path", "List": "inside, a path"}),
        ("inside another module, a path of its own body only", "module A = struct\n  module List = struct\n    let f x = List.rev x\n  end\nend\n", [], [], {"A": "top, no path", "List": "inside, a path"}),
        ("a module type is no module", "module type List = sig\n  type int\nend\n", [], ["int"], {}),
        ("module rec", "module rec Flambda : S = struct\n  let x = 1\nend\n", [], [], {"Flambda": "top, no path"}),
    ]
    fails = 0
    # the number of a line after a string that goes on after a backslash
    after = may_bind('let s = "one \\\n  line"\n\nlet max = 1\n')
    if after.values.get("max") != [4]:
        print("names: self-test: the line after a string of two lines: found %r, wanted [4]" % after.values.get("max"))
        fails += 1
    for what, text, values, types, modules in cases:
        got = may_bind(text)
        found = (
            sorted(n for n in asked if n in got.values),
            sorted(n for n in asked if n in got.types),
            {
                u: "extends" if d[0].extends else ("inside, " if d[0].inside else "top, ") + ("a path" if d[0].path_after else "no path")
                for u, d in got.modules.items()
            },
        )
        if found != (sorted(values), sorted(types), modules):
            print("names: self-test: %s: found %r, wanted %r" % (what, found, (sorted(values), sorted(types), modules)))
            fails += 1
    print("names: self-test: %d texts, %d not read as wanted" % (len(cases) + 1, fails))
    return 1 if fails else 0


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
