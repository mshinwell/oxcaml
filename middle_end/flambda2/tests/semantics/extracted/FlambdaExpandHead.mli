open BinNums
open FlambdaBindingTime
open FlambdaKindModel
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv

module Expanded_type : sig
  type head =
    | Head_value of head_of_kind_value
    | Head_naked_immediate of head_of_kind_naked_immediate
    | Head_naked_number of naked_number_kind * coq_Z list
    | Head_rec_info of unit
    | Head_region of unit

  val head_rect :
    (head_of_kind_value -> 'a1) ->
    (head_of_kind_naked_immediate -> 'a1) ->
    (naked_number_kind -> coq_Z list -> 'a1) ->
    (unit -> 'a1) ->
    (unit -> 'a1) ->
    head ->
    'a1

  val head_rec :
    (head_of_kind_value -> 'a1) ->
    (head_of_kind_naked_immediate -> 'a1) ->
    (naked_number_kind -> coq_Z list -> 'a1) ->
    (unit -> 'a1) ->
    (unit -> 'a1) ->
    head ->
    'a1

  type t =
    { kind : flambda_kind;
      descr : head or_unknown_or_bottom
    }

  val kind : t -> flambda_kind

  val descr : t -> head or_unknown_or_bottom

  val create_bottom : flambda_kind -> t

  val create_unknown : flambda_kind -> t

  val create_value : head_of_kind_value -> t

  val create_naked_immediate : head_of_kind_naked_immediate -> t

  val create_naked_number : naked_number_kind -> coq_Z list -> t

  val create_rec_info : unit -> t

  val create_region : unit -> t

  val create_const : const -> t

  val bottom_like : t -> t

  val unknown_like : t -> t

  val is_bottom : t -> bool

  val is_unknown : t -> bool

  val to_type : t -> flambda_type

  val of_non_alias_type : flambda_type -> t option
end

val expand_head_of_alias_type :
  Typing_env.t -> flambda_kind -> simple -> Expanded_type.t option

val expand_head0 :
  Typing_env.t -> flambda_type -> simple option -> Expanded_type.t option

val expand_head : Typing_env.t -> flambda_type -> Expanded_type.t option
