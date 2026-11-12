open BinInt
open BinNums
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv
open List

val insert_number : coq_Z -> coq_Z list -> coq_Z list

val sort_numbers : coq_Z list -> coq_Z list

val kind_of_simple : Typing_env.t -> simple -> flambda_kind option
