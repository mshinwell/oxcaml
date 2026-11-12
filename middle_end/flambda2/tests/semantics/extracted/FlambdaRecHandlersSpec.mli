open FlambdaModel
open FlambdaNormaliseSpec
open ListDef

val rewrite_rec_handlers : (expr -> expr) -> expr -> expr

val rewrite_rec_handlers_in_handler :
  (expr -> expr) -> continuation_handler -> continuation_handler

val rewrite_rec_handler :
  (expr -> expr) -> continuation_handler -> continuation_handler
