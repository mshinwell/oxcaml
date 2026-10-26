open AffineExpr
open FourierMotzkin
open LoopComparisons
open NaturalLoop
open SsaModel

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

val guard_test : block -> block -> (value * bool) option

val guard_facts :
  block ->
  (Affine.t list * Affine.t list) * ctx ->
  block ->
  (Affine.t list * Affine.t list) * ctx

val guards_at :
  ctx -> Affine.t list -> block -> (Affine.t list * Affine.t list) * ctx
