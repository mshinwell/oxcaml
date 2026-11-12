open BinPos
open FlambdaModel
open List

val binds_same_name : static_binding -> static_binding -> bool

val to_front :
  (static_binding -> bool) -> static_binding list -> static_binding list

val order_as : static_binding list -> static_binding list -> static_binding list

val order_statics_as : expr -> expr -> expr
