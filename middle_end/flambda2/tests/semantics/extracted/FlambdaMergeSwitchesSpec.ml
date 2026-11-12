open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open List
open ListDef
open PeanoNat

type arithmetic_kind =
  | Arithmetic_tagged
  | Arithmetic_naked

(** val standard_int_of_arithmetic_kind : arithmetic_kind -> standard_int **)

let standard_int_of_arithmetic_kind = function
  | Arithmetic_tagged -> Standard_tagged_immediate
  | Arithmetic_naked -> Standard_naked_immediate

type merge_by =
  | By_tagging
  | By_tagging_and_negating
  | As_it_is
  | By_arithmetic of arithmetic_kind * coq_Z * coq_Z

type arithmetic_step =
  | Multiply_by of coq_Z
  | Add_to of coq_Z
  | Subtract_from of coq_Z

(** val arithmetic_steps : coq_Z -> coq_Z -> coq_Z -> arithmetic_step list **)

let arithmetic_steps width offset slope =
  let negative = Z.ltb slope Z0 in
  let factor = if negative then wrap width (Z.opp slope) else slope in
  app
    (if Z.eqb factor (Zpos Coq_xH) then [] else Multiply_by factor :: [])
    (if negative
     then Subtract_from offset :: []
     else if Z.eqb offset Z0
     then []
     else Add_to offset :: [])

(** val arithmetic_step_value : coq_Z -> arithmetic_step -> coq_Z -> coq_Z
    option **)

let arithmetic_step_value width step a =
  let result =
   fun c r -> if in_range width c then Some (wrap width r) else None
  in
  match step with
  | Multiply_by c -> result c (Z.mul a c)
  | Add_to c -> result c (Z.add c a)
  | Subtract_from c -> result c (Z.sub c a)

(** val arithmetic_value : coq_Z -> arithmetic_step list -> coq_Z -> coq_Z
    option **)

let rec arithmetic_value width steps a =
  match steps with
  | [] -> Some a
  | step :: steps0 -> (
    match arithmetic_step_value width step a with
    | Some a0 -> arithmetic_value width steps0 a0
    | None -> None)

(** val constant_of_arm : merge_by -> coq_Z -> const option **)

let constant_of_arm how i =
  match how with
  | By_tagging ->
    if in_range (int_width Standard_naked_immediate) i
    then Some (Tagged_immediate i)
    else None
  | By_tagging_and_negating ->
    if Z.eqb i Z0
    then Some (Tagged_immediate (Zpos Coq_xH))
    else if Z.eqb i (Zpos Coq_xH)
    then Some (Tagged_immediate Z0)
    else None
  | As_it_is -> Some (Naked_immediate i)
  | By_arithmetic (kind, offset, slope) ->
    let standard = standard_int_of_arithmetic_kind kind in
    let width = int_width standard in
    if in_range width i
    then
      option_map (const_of_int standard)
        (arithmetic_value width (arithmetic_steps width offset slope) i)
    else None

(** val merged_arguments : variable -> simple list -> simple list -> simple list
    **)

let rec merged_arguments v args args' =
  match args with
  | [] -> []
  | s :: args0 -> (
    match args' with
    | [] -> []
    | s' :: args'0 ->
      (if simple_eq_dec s s' then s else Var v)
      :: merged_arguments v args0 args'0)

(** val constant_for : variable -> const -> simple -> simple **)

let constant_for v c s =
  match s with Var x -> if Pos.eqb x v then Const c else s | _ -> s

(** val arm_is_merged : merge_by -> variable -> apply_cont -> (coq_Z *
    apply_cont) -> bool **)

let arm_is_merged how v merged arm =
  match constant_of_arm how (fst arm) with
  | Some c ->
    if
      apply_cont_eq_dec (snd arm)
        { ac_continuation = merged.ac_continuation;
          ac_args = map (constant_for v c) merged.ac_args;
          ac_trap_action = merged.ac_trap_action
        }
    then true
    else false
  | None -> false

(** val bind_tagged : variable -> expr -> expr **)

let bind_tagged v body =
  Let (v, Value, Prim (Unary Tag_immediate, Var v :: []), body)

(** val bind_negated : variable -> expr -> expr **)

let bind_negated v body =
  Let (v, Value, Prim (Unary Boolean_not, Var v :: []), body)

(** val bind_arithmetic_step : standard_int -> variable -> arithmetic_step ->
    expr -> expr **)

let bind_arithmetic_step standard v step body =
  let constant = fun c -> Const (const_of_int standard c) in
  let arith = fun op args -> Prim (Binary (Int_arith (standard, op)), args) in
  Let
    ( v,
      kind_of_standard_int standard,
      (match step with
      | Multiply_by c -> arith Mul [Var v; constant c]
      | Add_to c -> arith Add [constant c; Var v]
      | Subtract_from c -> arith Sub [constant c; Var v]),
      body )

(** val bind_arithmetic_steps : standard_int -> variable -> arithmetic_step list
    -> expr -> expr **)

let rec bind_arithmetic_steps standard v steps body =
  match steps with
  | [] -> body
  | step :: steps0 ->
    bind_arithmetic_step standard v step
      (bind_arithmetic_steps standard v steps0 body)

(** val bind_arithmetic : arithmetic_kind -> coq_Z -> coq_Z -> variable -> expr
    -> expr **)

let bind_arithmetic kind offset slope v body =
  let standard = standard_int_of_arithmetic_kind kind in
  let body0 =
    bind_arithmetic_steps standard v
      (arithmetic_steps (int_width standard) offset slope)
      body
  in
  match kind with
  | Arithmetic_tagged -> bind_tagged v body0
  | Arithmetic_naked -> body0

(** val first_difference : simple list -> simple list -> (const * const) option
    **)

let rec first_difference args args' =
  match args with
  | [] -> None
  | s :: args0 -> (
    match args' with
    | [] -> None
    | s' :: args'0 -> (
      if simple_eq_dec s s'
      then first_difference args0 args'0
      else
        match s with
        | Const c -> ( match s' with Const c' -> Some (c, c') | _ -> None)
        | _ -> None))

(** val line_through : coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> (coq_Z *
    coq_Z) option **)

let line_through width i a i' a' =
  let run = wrap width (Z.sub i' i) in
  let rise = wrap width (Z.sub a' a) in
  if Z.eqb run Z0 || negb (Z.eqb (Z.rem rise run) Z0)
  then None
  else
    let slope = wrap width (Z.quot rise run) in
    Some (wrap width (Z.sub a (Z.mul slope i)), slope)

(** val arithmetic_of_arms : coq_Z -> coq_Z -> simple list -> simple list ->
    ((arithmetic_kind * coq_Z) * coq_Z) option **)

let arithmetic_of_arms i i' args args' =
  let line =
   fun kind a a' ->
    let width = int_width (standard_int_of_arithmetic_kind kind) in
    match line_through width i a i' a' with
    | Some p ->
      let offset, slope = p in
      Some ((kind, offset), slope)
    | None -> None
  in
  match first_difference args args' with
  | Some p -> (
    let c, c' = p in
    match c with
    | Naked_immediate a -> (
      match c' with
      | Naked_immediate a' -> line Arithmetic_naked a a'
      | _ -> None)
    | Tagged_immediate a -> (
      match c' with
      | Tagged_immediate a' -> line Arithmetic_tagged a a'
      | _ -> None)
    | _ -> None)
  | None -> None

(** val merge_switch : simple -> (coq_Z * apply_cont) list -> expr **)

let merge_switch scrutinee arms =
  match scrutinee with
  | Var v -> (
    match arms with
    | [] -> Switch (scrutinee, arms)
    | p :: l -> (
      let i, ac = p in
      match l with
      | [] -> Switch (scrutinee, arms)
      | p0 :: _ ->
        let i', ac' = p0 in
        let merged =
          { ac_continuation = ac.ac_continuation;
            ac_args = merged_arguments v ac.ac_args ac'.ac_args;
            ac_trap_action = None
          }
        in
        if var_in_simples v merged.ac_args
        then
          if forallb (arm_is_merged By_tagging v merged) arms
          then bind_tagged v (Apply_cont merged)
          else if forallb (arm_is_merged By_tagging_and_negating v merged) arms
          then bind_tagged v (bind_negated v (Apply_cont merged))
          else if forallb (arm_is_merged As_it_is v merged) arms
          then Apply_cont merged
          else
            match arithmetic_of_arms i i' ac.ac_args ac'.ac_args with
            | Some p1 ->
              let p2, slope = p1 in
              let kind, offset = p2 in
              if
                Nat.leb (S (S (S O))) (length arms)
                && forallb
                     (arm_is_merged
                        (By_arithmetic (kind, offset, slope))
                        v merged)
                     arms
              then bind_arithmetic kind offset slope v (Apply_cont merged)
              else Switch (scrutinee, arms)
            | None -> Switch (scrutinee, arms)
        else Switch (scrutinee, arms)))
  | _ -> Switch (scrutinee, arms)

(** val merge_switches : expr -> expr **)

let rec merge_switches e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, merge_switches body)
  | Let_static (bindings, body) -> Let_static (bindings, merge_switches body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler (params, metadata, merge_switches handler),
        merge_switches body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, merge_switches body)
  | Switch (scrutinee, arms) -> merge_switch scrutinee arms
  | _ -> e
