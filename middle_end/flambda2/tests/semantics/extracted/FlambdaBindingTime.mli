open BinInt
open BinNums

module Name_mode : sig
  type t =
    | Normal
    | Phantom
    | In_types

  val normal : t

  val in_types : t

  val compare_partial_order : t -> t -> coq_Z option

  val equal : t -> t -> bool
end

module Binding_time : sig
  module Coq__1 : sig
    type t = coq_Z
  end

  include module type of struct
    include Coq__1
  end

  val strictly_earlier : t -> t -> bool

  val consts : t

  val symbols : t

  val imported_variables : t

  val earliest_var : t

  val succ : t -> t

  val equal : t -> t -> bool

  module With_name_mode : sig
    type t =
      { binding_time : Coq__1.t;
        name_mode : Name_mode.t
      }

    val binding_time : t -> Coq__1.t

    val name_mode : t -> Name_mode.t

    val symbols : t

    val consts : t

    val imported_variables : t

    val scoped_name_mode : t -> Coq__1.t -> Name_mode.t
  end
end
