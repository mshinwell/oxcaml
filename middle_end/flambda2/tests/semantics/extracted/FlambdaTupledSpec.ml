open BinInt
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaNominalSpec
open FlambdaPrimitiveModel
open FlambdaSemanticsSpec

(** val let_tuple_fields : variable list -> nat -> nat -> simple -> expr -> expr
    **)

let rec let_tuple_fields params size field tuple body =
  match params with
  | [] -> body
  | param :: params0 ->
    Let
      ( param,
        Value,
        Prim
          ( Unary (Block_load (tuple_access size, Immutable, Z.of_nat field)),
            tuple :: [] ),
        let_tuple_fields params0 size (S field) tuple body )

(** val inlined_tupled_body : code -> renaming -> apply_expr -> simple -> expr **)

let inlined_tupled_body c r ap tuple =
  Let
    ( code_my_closure c,
      Value,
      Simple ap.ap_callee,
      let_tuple_fields (code_params c)
        (length (code_params c))
        O tuple
        (rename_expr r (code_body c)) )

(** val inlined_tupled_call : code -> renaming -> apply_expr -> expr **)

let inlined_tupled_call c r ap =
  match ap.ap_args with
  | [] -> Apply ap
  | tuple :: l -> (
    match l with [] -> inlined_tupled_body c r ap tuple | _ :: _ -> Apply ap)
