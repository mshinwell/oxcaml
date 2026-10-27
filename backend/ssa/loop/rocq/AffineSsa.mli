open AffineExpr
open FourierMotzkin
open LoopComparisons
open SsaModel

type ctx =
  { atoms : (int * Ssa.finished Ssa.Value.t) list;
    next : int;
    budget : int
  }

val new_ctx : ctx

val refill : ctx -> ctx

val spend : ctx -> int -> ctx

val intern : ctx -> Ssa.finished Ssa.Value.t -> int * ctx

val atomize : ctx -> Ssa.finished Ssa.Value.t -> (t * Range.t option) * ctx

val keep :
  ctx ->
  Ssa.finished Ssa.Value.t ->
  t ->
  Range.t option ->
  (t * Range.t option) * ctx

val radd : Range.t option -> Range.t option -> Range.t option

val rsub : Range.t option -> Range.t option -> Range.t option

val rscale : int -> Range.t option -> Range.t option

val expr_of_value :
  ctx -> Ssa.finished Ssa.Value.t -> (t * Range.t option) * ctx

val push_sides : Affine.t list -> Affine.t list -> Affine.t list

val linearize :
  ctx ->
  Affine.t list ->
  Ssa.finished Ssa.Value.t ->
  (Affine.t * Affine.t list) * ctx

val cond_facts :
  ctx ->
  Affine.t list ->
  bool ->
  Ssa.finished Ssa.Value.t ->
  (Affine.t list * Affine.t list) * ctx

val guard_test : block -> block -> (Ssa.finished Ssa.Value.t * bool) option

val guard_facts :
  block ->
  (Affine.t list * Affine.t list) * ctx ->
  block ->
  (Affine.t list * Affine.t list) * ctx

val guards_at :
  ctx -> Affine.t list -> block -> (Affine.t list * Affine.t list) * ctx
