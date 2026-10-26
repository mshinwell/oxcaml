val add_fits : int -> int -> bool

val mul_fits : int -> int -> bool

val add_ovf : int -> int -> int option

val mul_ovf : int -> int -> int option

val neg_ovf : int -> int option

val coeff_gen : 'a1 -> int -> (int * 'a1) list -> 'a1

module Affine : sig
  type t =
    { const : int;
      terms : (int * int) list
    }

  val const : t -> int

  val terms : t -> (int * int) list

  val constant : int -> t

  val var : int -> t

  val coeff : int -> t -> int

  val terms_equal : (int * int) list -> (int * int) list -> bool

  val equal : t -> t -> bool

  val add_const : t -> int -> t

  val add : t -> t -> t

  val scale : int -> t -> t

  val neg : t -> t

  val sub : t -> t -> t

  val scale_checked : int -> t -> t option

  val add_checked : t -> t -> t option

  val add_const_checked : t -> int -> t option

  val sub_checked : t -> t -> t option
end

val add_fits64 : int64 -> int64 -> bool

val mul_fits64 : int64 -> int64 -> bool

val add_ovf64 : int64 -> int64 -> int64 option

val mul_ovf64 : int64 -> int64 -> int64 option

val gcd64 : int64 -> int64 -> int64

val fdiv64 : int64 -> int64 -> int64

val to_int_ovf : int64 -> int option

val coeff64 : int -> (int * int64) list -> int64

val scaled : int64 -> Affine.t -> (int64 * (int * int64) list) option

val resolvent : int -> int -> Affine.t -> Affine.t -> Affine.t option

val elim : int -> Affine.t list -> Affine.t list option

val elim_all : int list -> Affine.t list -> Affine.t list option

val feasible : Affine.t list -> bool

val entails : Affine.t list -> Affine.t -> bool
