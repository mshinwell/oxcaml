# What units made from OCaml sources need that the model has not got

From V2 (the corpus), for whoever adds constructs to the model and
rewrites to the validator. The units are made by
`middle_end/flambda2/tests/semantics/ocaml/from_ocaml.sh`
(`-drawfexpr`); each fragment below is what the front end prints.
Ranked by how much OCaml each one blocks: the first ones are in almost
every program.

Three states of a unit, as the test tool reports them: **not checked**
(the conversion refuses a construct), **the same, not validated** (the
two runs agree, the validator cannot match the terms), **undefined
before** (the model has no step for the source, so anything passes: the
worst of the three, as it looks like a pass).

## 1. Not checked: constructs and primitives

| Rank | Construct | OCaml that makes it | Fragment |
|------|-----------|---------------------|----------|
| 1 | `Phys_equal` on immediates | `=` and `<>` on `int`, a match on an integer constant, `if n = 0` | `let prim = %phys_eq (n, 0) in let eq = %tag_imm (prim) in let untagged = %untag_imm (eq) in switch untagged ...`; `%phys_ne` for `<>` |
| 2 | Regions and local allocation | an argument or a closure that does not escape, a local function | `let region = %begin_region () in let ghost_region = %begin_ghost_region () in ... let b = %block.[0].toplevel.local[region] (x) in ... let unit = %end_region (region) in let unit = %end_ghost_region (ghost_region) in ...`; a closure: `closure g_8 @g &my_alloc_region &region with { x = x }`; a call: `apply direct(f &toplevel &region &ghost_region) ...` |
| 3 | Trap actions and `raise` | integer division and `mod` (even by a constant), `assert`, array access, `raise`, `try` | `(let prim = %int_comp.ne (4, 0) in switch prim \| 0 -> k1 \| 1 -> k2) where k1 = cont error pop(regular error) ($`*predef*`.caml_exn_Division_by_zero)` |
| 4 | `Boolean_not` | `not b` | `let Pnot = %boolean_not (b) in ...` |
| 5 | `Num_conv` between integer kinds | `for` loops (the counter is a naked `int64`), `Int64.of_int`, `Int64.to_int` | `let prim = %untag_imm (n) in let c = %num_conv.[imm].[int64] (prim) in ...`; `let prim = %num_conv.[int64].[imm] (counter) in let i = %tag_imm (prim) in ...` |
| 6 | `Int_shift` | `lsl`, `lsr`, `asr` | `let prim = %untag_imm (2) in let s = %int_shift.lsl (x, prim) in ...` |
| 7 | Float arithmetic and comparison | `+.`, `<` on floats | `let a = %unbox_num.float (x) in let b = %unbox_num.float (y) in let c = %bfloat_arith.add (a, b) in let r = %box_num.float.toplevel (c) in ...` |
| 8 | Mutable blocks | a reference or a mutable record field that escapes | `%block_load` with `Mutable`, `%block_set` |
| 9 | Arrays | `a.(i)` | `Array_load`, with a bounds check that raises |
| 10 | C calls | polymorphic comparison, `exception E` (`caml_fresh_oo_id`), anything of the runtime | `apply ccall ($`*extern*`.caml_equal : val * val -> val) (x, y) -> k * error`; this does not parse back (below) |

Not blocking, because the conversion drops them (a hack, with CRs):
`let next_depth = rec_info (succ my_depth)` at the head of every
function, `my_depth`, and the coercion `~ depth my_depth -> next_depth`
on the callee of a recursive call.

On 2: stack allocation cannot be turned off by a flag (it is fixed when
the compiler is configured). A type annotation on the function keeps
its argument on the heap, which is how the examples avoid it. In the
terms seen, a region always comes with a local allocation in it.

## 2. Undefined before: the model has no step for a defined program

| Construct | OCaml that makes it | What the model does | What it should do |
|-----------|---------------------|---------------------|-------------------|
| A tupled function | `let f (x, y) = ...` called through its closure | the code has two parameters and `tupled`; the call passes one block; the conversion drops `tupled` and the machine finds an arity mismatch | the conversion should refuse `tupled` code until the model has it |
| Partial application through an unknown function | `let app f x = f x` then `app add 1` | an indirect call with fewer arguments than parameters is undefined | make the closure of the remaining parameters (`caml_curry`) |
| Over-application through an unknown function | `let app2 f x y = f x y` then `app2 adder 1 2` | an indirect call with more arguments than parameters is undefined | call with the first, then call the result with the rest (`caml_apply`) |

(Where the function is known when the term is made, the front end
splits an over-application into two calls and makes a stub for a
partial one, and these do run.)

## 3. The same, not validated: rewrites the validator has not got

| Rank | What Simplify does | OCaml that shows it | State |
|------|--------------------|---------------------|-------|
| 1 | Lifts a closed closure, block or boxed number at toplevel to a symbol | any function that stays (recursive, not inlined, or exported), any block that stays | not started; a simulation proof of the size of `FlambdaUnusedStaticsProofs.v`, with a new law of the primitives |
| 2 | Loads a field, the tag or `Is_int` of a known block | every unit (the module block), every match on a constructor just applied | done: `FlambdaBlockLoadSpec.v` |
| 3 | Deletes a continuation that is not used | every match resolved | done: `FlambdaUnusedContsSpec.v` |
| 4 | Unboxes a number it has seen boxed | arithmetic on `int64`, `float` | next |
| 5 | Rewrites inside the handler of a recursive continuation; removes a parameter of a continuation that is not used; inlines a continuation applied once that is not at the end of its scope | `while` loops | not started |
| 6 | Makes a self tail call a jump (loopify) | tail-recursive functions | not started |
| 7 | Identities of arithmetic (`x + 0`) | here and there | not started |

## 4. The printer and the parser of fexpr

- A C call is printed `apply ccall [noalloc] (...)` and the parser
  wants `ccall [noalloc] &<region>`: a unit with a C call that
  `-drawfexpr` prints is a syntax error when read back. The same for a
  method call.
- `Make_block` is printed without the kinds of its fields, and read
  back with `any_value` for each. So the term the tool gives to
  Simplify is not the term the compiler gives it: it says less of the
  fields. The conversion's refusal of a field kind other than
  `any_value` never fires on a term that was parsed.
- A direct call is printed without the arity of its parameters.
