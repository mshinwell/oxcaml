open AffineSsa
open FourierMotzkin
open InductionVar
open LoopComparisons
open NaturalLoop
open SsaModel

type t =
  | Terminates
  | Unknown

type exit_branch =
  { condition : value;
    continue_when_true : bool;
    exit_target : block
  }

val find_exit_branch : natural_loop -> exit_branch option

type bound =
  | Value_bound of value
  | Const_bound of int

val bound_in_range : int -> block -> bound -> bool

val extract_comparison :
  (value -> bool) ->
  (value -> bool) ->
  value ->
  ((Cmm.integer_comparison * bool) * bound) option

val biv_implies_termination : op_def -> biv -> bool

val analyze : op_def -> natural_loop -> biv list -> t
