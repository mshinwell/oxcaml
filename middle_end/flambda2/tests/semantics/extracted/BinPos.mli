open BinNums

module Pos : sig
  val eqb : positive -> positive -> bool

  val eq_dec : positive -> positive -> bool
end
