open AffineExpr
open FourierMotzkin
open LoopComparisons

type value = Ssa.finished Ssa.Value.t

type tree =
  | Const_int of value * int64
  | Iadd of value * tree * tree
  | Isub of value * tree * tree
  | Iadd_imm of value * tree * int
  | Isub_imm of value * tree * int
  | Ilsl of value * tree * int
  | Iasr of value * tree * int
  | Ilsr of value * int
  | Ior of value * tree * int
  | Icomp of value * Cmm.integer_comparison * tree * tree
  | Icomp_imm of value * Cmm.integer_comparison * tree * int
  | Other of value

val root : tree -> value

type ctx =
  { atoms : (int * value) list;
    next : int
  }

val new_ctx : ctx

val intern : ctx -> value -> int * ctx

val fits_int : int64 -> bool

val atomize : ctx -> value -> (t * Range.t option) * ctx

val keep : ctx -> value -> t -> Range.t option -> (t * Range.t option) * ctx

val radd : Range.t option -> Range.t option -> Range.t option

val rsub : Range.t option -> Range.t option -> Range.t option

val rscale : int -> Range.t option -> Range.t option

val expr_of_value : ctx -> tree -> (t * Range.t option) * ctx

val push_sides : Affine.t list -> Affine.t list -> Affine.t list

val linearize : ctx -> Affine.t list -> tree -> (Affine.t * Affine.t list) * ctx

val cond_facts :
  ctx -> Affine.t list -> bool -> tree -> (Affine.t list * Affine.t list) * ctx
