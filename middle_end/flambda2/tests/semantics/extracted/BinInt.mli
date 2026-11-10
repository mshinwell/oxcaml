open BinNums
open BinPos
open PosDef

module Z : sig
  val eqb : coq_Z -> coq_Z -> bool

  val eq_dec : coq_Z -> coq_Z -> bool
end
