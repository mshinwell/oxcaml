open BinInt
open BinNums
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaTypeGrammar
open FlambdaTypingEnv
open List

(** val insert_number : coq_Z -> coq_Z list -> coq_Z list **)

let rec insert_number i sorted =
  match sorted with
  | [] -> i :: []
  | j :: rest -> if Z.leb i j then i :: sorted else j :: insert_number i rest

(** val sort_numbers : coq_Z list -> coq_Z list **)

let sort_numbers numbers = fold_right insert_number [] numbers

(** val kind_of_simple : Typing_env.t -> simple -> flambda_kind option **)

let kind_of_simple tenv = function
  | Var x -> option_map kind (Typing_env.find tenv (Name_var x) None)
  | Symbol _ -> Some Value
  | Const c -> Some (kind_of_const c)
