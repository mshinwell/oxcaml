open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
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

(** val arithmetic_of_constants : coq_Z -> coq_Z -> const -> const ->
    ((arithmetic_kind * coq_Z) * coq_Z) option **)

let arithmetic_of_constants i i' c c' =
  let line =
   fun kind a a' ->
    let width = int_width (standard_int_of_arithmetic_kind kind) in
    match line_through width i a i' a' with
    | Some p ->
      let offset, slope = p in
      Some ((kind, offset), slope)
    | None -> None
  in
  match c with
  | Naked_immediate a -> (
    match c' with Naked_immediate a' -> line Arithmetic_naked a a' | _ -> None)
  | Tagged_immediate a -> (
    match c' with
    | Tagged_immediate a' -> line Arithmetic_tagged a a'
    | _ -> None)
  | _ -> None

(** val arithmetic_of_arms : coq_Z -> coq_Z -> simple list -> simple list ->
    ((arithmetic_kind * coq_Z) * coq_Z) option **)

let arithmetic_of_arms i i' args args' =
  match first_difference args args' with
  | Some p ->
    let c, c' = p in
    arithmetic_of_constants i i' c c'
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

type argument_way =
  | Same_in_every_arm of simple
  | Computed of merge_by

(** val argument_in_arm : coq_Z -> argument_way -> simple option **)

let argument_in_arm i = function
  | Same_in_every_arm s -> Some s
  | Computed how -> option_map (fun x -> Const x) (constant_of_arm how i)

(** val arguments_in_arm : coq_Z -> argument_way list -> simple list option **)

let rec arguments_in_arm i = function
  | [] -> Some []
  | way :: ways0 -> (
    match argument_in_arm i way with
    | Some s -> (
      match arguments_in_arm i ways0 with
      | Some args -> Some (s :: args)
      | None -> None)
    | None -> None)

(** val arm_has_ways : continuation -> argument_way list -> (coq_Z * apply_cont)
    -> bool **)

let arm_has_ways k ways arm =
  match arguments_in_arm (fst arm) ways with
  | Some args ->
    if
      apply_cont_eq_dec (snd arm)
        { ac_continuation = k; ac_args = args; ac_trap_action = None }
    then true
    else false
  | None -> false

(** val column_of_arms : (coq_Z * simple list) list -> (coq_Z * simple) list
    option **)

let rec column_of_arms = function
  | [] -> Some []
  | p :: rows0 -> (
    let i, l = p in
    match l with
    | [] -> None
    | s :: _ -> (
      match column_of_arms rows0 with
      | Some column -> Some ((i, s) :: column)
      | None -> None))

(** val rest_of_arms : (coq_Z * simple list) list -> (coq_Z * simple list) list
    **)

let rest_of_arms rows = map (fun row -> fst row, tl (snd row)) rows

(** val column_is_computed : merge_by -> (coq_Z * simple) list -> bool **)

let column_is_computed how column =
  forallb
    (fun entry ->
      match constant_of_arm how (fst entry) with
      | Some c -> if simple_eq_dec (snd entry) (Const c) then true else false
      | None -> false)
    column

(** val way_of_column : (coq_Z * simple) list -> argument_way option **)

let way_of_column column =
  match column with
  | [] -> None
  | p :: l -> (
    let i, s = p in
    match l with
    | [] -> None
    | p0 :: _ -> (
      let i', s' = p0 in
      if
        forallb
          (fun entry -> if simple_eq_dec s (snd entry) then true else false)
          column
      then Some (Same_in_every_arm s)
      else if column_is_computed By_tagging column
      then Some (Computed By_tagging)
      else if column_is_computed By_tagging_and_negating column
      then Some (Computed By_tagging_and_negating)
      else if column_is_computed As_it_is column
      then Some (Computed As_it_is)
      else
        match s with
        | Const c -> (
          match s' with
          | Const c' -> (
            match arithmetic_of_constants i i' c c' with
            | Some p1 ->
              let p2, slope = p1 in
              let kind, offset = p2 in
              if
                Nat.leb (S (S (S O))) (length column)
                && column_is_computed
                     (By_arithmetic (kind, offset, slope))
                     column
              then Some (Computed (By_arithmetic (kind, offset, slope)))
              else None
            | None -> None)
          | _ -> None)
        | _ -> None))

(** val ways_of_arguments : nat -> (coq_Z * simple list) list -> argument_way
    list option **)

let rec ways_of_arguments count rows =
  match count with
  | O -> Some []
  | S count0 -> (
    match column_of_arms rows with
    | Some column -> (
      match way_of_column column with
      | Some way -> (
        match ways_of_arguments count0 (rest_of_arms rows) with
        | Some ways -> Some (way :: ways)
        | None -> None)
      | None -> None)
    | None -> None)

(** val bind_tagged_to : variable -> variable -> expr -> expr **)

let bind_tagged_to v x body =
  Let (x, Value, Prim (Unary Tag_immediate, Var v :: []), body)

(** val bind_same_to : variable -> variable -> expr -> expr **)

let bind_same_to v x body = Let (x, naked_immediate_kind, Simple (Var v), body)

(** val bind_way : merge_by -> variable -> variable -> expr -> expr **)

let bind_way how v x body =
  match how with
  | By_tagging -> bind_tagged_to v x body
  | By_tagging_and_negating -> bind_tagged_to v x (bind_negated x body)
  | As_it_is -> body
  | By_arithmetic (kind, offset, slope) -> (
    let standard = standard_int_of_arithmetic_kind kind in
    let body0 =
      bind_arithmetic_steps standard x
        (arithmetic_steps (int_width standard) offset slope)
        body
    in
    match kind with
    | Arithmetic_tagged -> bind_tagged_to v x body0
    | Arithmetic_naked -> bind_same_to v x body0)

(** val bind_ways : variable -> variable list -> argument_way list -> expr ->
    expr **)

let rec bind_ways v names ways body =
  match names with
  | [] -> body
  | x :: names0 -> (
    match ways with
    | [] -> body
    | way :: ways0 -> (
      let body0 = bind_ways v names0 ways0 body in
      match way with
      | Same_in_every_arm _ -> body0
      | Computed how -> bind_way how v x body0))

(** val merged_by_ways : variable -> variable list -> argument_way list ->
    simple list **)

let rec merged_by_ways v names ways =
  match names with
  | [] -> []
  | x :: names0 -> (
    match ways with
    | [] -> []
    | way :: ways0 ->
      (match way with
      | Same_in_every_arm s -> s
      | Computed how -> ( match how with As_it_is -> Var v | _ -> Var x))
      :: merged_by_ways v names0 ways0)

(** val names_usable : variable -> variable list -> argument_way list -> bool **)

let names_usable v names ways =
  ((Nat.eqb (length names) (length ways) && distinct names)
  && negb (among v names))
  && forallb
       (fun way ->
         match way with
         | Same_in_every_arm s ->
           negb (existsb (fun x -> var_in_simple x s) names)
         | Computed _ -> true)
       ways

(** val merge_switch_by_arguments : variable list -> simple -> (coq_Z *
    apply_cont) list -> expr option **)

let merge_switch_by_arguments names scrutinee arms =
  match scrutinee with
  | Var v -> (
    match arms with
    | [] -> None
    | p :: l -> (
      let _, ac = p in
      match l with
      | [] -> None
      | _ :: _ -> (
        let k = ac.ac_continuation in
        match
          ways_of_arguments (length ac.ac_args)
            (map (fun arm -> fst arm, (snd arm).ac_args) arms)
        with
        | Some ways ->
          if names_usable v names ways && forallb (arm_has_ways k ways) arms
          then
            Some
              (bind_ways v names ways
                 (Apply_cont
                    { ac_continuation = k;
                      ac_args = merged_by_ways v names ways;
                      ac_trap_action = None
                    }))
          else None
        | None -> None)))
  | _ -> None

type known_continuations = (continuation * variable list) list

(** val parameters_of_handler : continuation_handler -> variable list **)

let parameters_of_handler = function Handler (params, _, _) -> params

(** val merge_switch_knowing : known_continuations -> simple -> (coq_Z *
    apply_cont) list -> expr **)

let merge_switch_knowing known scrutinee arms =
  match merge_switch scrutinee arms with
  | Switch (_, _) -> (
    match arms with
    | [] -> Switch (scrutinee, arms)
    | p :: _ -> (
      let _, ac = p in
      match lookup ac.ac_continuation known with
      | Some names -> (
        match merge_switch_by_arguments names scrutinee arms with
        | Some merged -> merged
        | None -> Switch (scrutinee, arms))
      | None -> Switch (scrutinee, arms)))
  | x -> x

(** val merge_switches_knowing : known_continuations -> expr -> expr **)

let rec merge_switches_knowing known e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, merge_switches_knowing known body)
  | Let_static (bindings, body) ->
    Let_static (bindings, merge_switches_knowing known body)
  | Let_cont_non_recursive (k, handler0, body) ->
    let (Handler (params, metadata, handler)) = handler0 in
    Let_cont_non_recursive
      ( k,
        Handler (params, metadata, merge_switches_knowing known handler),
        merge_switches_knowing ((k, params) :: known) body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( handlers,
        merge_switches_knowing
          (app
             (map
                (fun entry -> fst entry, parameters_of_handler (snd entry))
                handlers)
             known)
          body )
  | Switch (scrutinee, arms) -> merge_switch_knowing known scrutinee arms
  | _ -> e

(** val merge_switches : expr -> expr **)

let merge_switches e = merge_switches_knowing [] e
