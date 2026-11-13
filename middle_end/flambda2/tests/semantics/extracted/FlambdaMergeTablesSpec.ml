open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaMergeSwitchesSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaPrimitiveSpec
open FlambdaSemanticsSpec
open List
open ListDef
open OxCamlOption
open PeanoNat

type known_tables = (symbol * simple list) list

(** val element_closed : simple -> bool **)

let element_closed element = is_some (eval_simple [] element)

(** val table_of_binding : static_binding -> known_tables **)

let table_of_binding = function
  | Bind_symbol (s, const) -> (
    match const with
    | Static_const_immutable_value_array elements ->
      if forallb element_closed elements then (s, elements) :: [] else []
    | _ -> [])
  | _ -> []

(** val tables_under_statics : known_tables -> static_binding list ->
    known_tables **)

let tables_under_statics tables bindings =
  app (flat_map table_of_binding bindings) tables

(** val table_offset : coq_Z -> coq_Z **)

let table_offset first =
  wrap (int_width Standard_tagged_immediate) (Z.opp first)

(** val table_index : coq_Z -> coq_Z -> coq_Z -> coq_Z option **)

let table_index first offset i =
  let width = int_width Standard_tagged_immediate in
  if in_range (int_width Standard_naked_immediate) i
  then
    if Z.eqb first Z0
    then Some i
    else if in_range width offset
    then Some (wrap width (Z.add i offset))
    else None
  else None

(** val table_element : coq_Z -> coq_Z -> simple list -> coq_Z -> simple option
    **)

let table_element first offset elements i =
  match table_index first offset i with
  | Some index ->
    if Z.leb Z0 index && Z.ltb index (Z.of_nat (length elements))
    then nth_error elements (Z.to_nat index)
    else None
  | None -> None

(** val all_immediates : simple list -> bool **)

let all_immediates elements =
  forallb
    (fun element ->
      match eval_simple [] element with
      | Some w -> is_tagged_immediate w
      | None -> false)
    elements

(** val table_array_kind : bool -> array_kind **)

let table_array_kind = function
  | true -> Array_immediates
  | false -> Array_values

(** val table_load_kind : bool -> array_load_kind **)

let table_load_kind = function true -> Load_immediates | false -> Load_values

(** val element_taken : bool -> simple -> bool **)

let element_taken immediates element =
  immediates
  ||
  match eval_simple [] element with
  | Some w -> array_element_ok Array_values w
  | None -> false

(** val element_for : variable -> simple -> simple -> simple **)

let element_for v element s =
  match s with Var x -> if Pos.eqb x v then element else s | _ -> s

(** val merged_across : variable -> simple list -> (coq_Z * apply_cont) list ->
    simple list **)

let rec merged_across v args = function
  | [] -> args
  | arm :: arms0 ->
    merged_across v (merged_arguments v args (snd arm).ac_args) arms0

(** val arm_is_loaded : variable -> apply_cont -> coq_Z -> coq_Z -> simple list
    -> bool -> (coq_Z * apply_cont) -> bool **)

let arm_is_loaded v merged first offset elements immediates arm =
  match table_element first offset elements (fst arm) with
  | Some element ->
    element_taken immediates element
    &&
    if
      apply_cont_eq_dec (snd arm)
        { ac_continuation = merged.ac_continuation;
          ac_args = map (element_for v element) merged.ac_args;
          ac_trap_action = merged.ac_trap_action
        }
    then true
    else false
  | None -> false

(** val bind_table_offset : variable -> coq_Z -> coq_Z -> expr -> expr **)

let bind_table_offset v first offset body =
  if Z.eqb first Z0
  then body
  else
    Let
      ( v,
        Value,
        Prim
          ( Binary (Int_arith (Standard_tagged_immediate, Add)),
            [Var v; Const (Tagged_immediate offset)] ),
        body )

(** val bind_table_load : variable -> symbol -> coq_Z -> coq_Z -> bool -> expr
    -> expr **)

let bind_table_load v s first offset immediates body =
  bind_tagged v
    (bind_table_offset v first offset
       (Let
          ( v,
            Value,
            Prim
              ( Binary
                  (Array_load
                     ( table_array_kind immediates,
                       table_load_kind immediates,
                       Immutable )),
                [Symbol s; Var v] ),
            body )))

(** val table_has_arms : variable -> apply_cont -> coq_Z -> coq_Z -> (coq_Z *
    apply_cont) list -> (symbol * simple list) -> bool **)

let table_has_arms v merged first offset arms table =
  Nat.eqb (length (snd table)) (length arms)
  &&
  let immediates = all_immediates (snd table) in
  forallb (arm_is_loaded v merged first offset (snd table) immediates) arms

(** val merge_switch_by_table : known_tables -> simple -> (coq_Z * apply_cont)
    list -> expr option **)

let merge_switch_by_table tables scrutinee arms =
  match scrutinee with
  | Var v -> (
    match arms with
    | [] -> None
    | p :: others -> (
      let first, ac = p in
      match others with
      | [] -> None
      | _ :: l -> (
        match l with
        | [] -> None
        | _ :: _ ->
          let merged =
            { ac_continuation = ac.ac_continuation;
              ac_args = merged_across v ac.ac_args others;
              ac_trap_action = None
            }
          in
          if var_in_simples v merged.ac_args
          then
            let offset = table_offset first in
            match find (table_has_arms v merged first offset arms) tables with
            | Some p0 ->
              let s, elements = p0 in
              Some
                (bind_table_load v s first offset (all_immediates elements)
                   (Apply_cont merged))
            | None -> None
          else None)))
  | _ -> None

type table_way =
  | Without_table of argument_way
  | From_table of symbol * simple list * bool

(** val is_from_table : table_way -> bool **)

let is_from_table = function
  | Without_table _ -> false
  | From_table (_, _, _) -> true

(** val argument_by_table_way : coq_Z -> coq_Z -> coq_Z -> table_way -> simple
    option **)

let argument_by_table_way first offset i = function
  | Without_table way0 -> argument_in_arm i way0
  | From_table (_, elements, immediates) -> (
    match table_element first offset elements i with
    | Some element ->
      if element_taken immediates element then Some element else None
    | None -> None)

(** val arguments_by_table_ways : coq_Z -> coq_Z -> coq_Z -> table_way list ->
    simple list option **)

let rec arguments_by_table_ways first offset i = function
  | [] -> Some []
  | way :: ways0 -> (
    match argument_by_table_way first offset i way with
    | Some s -> (
      match arguments_by_table_ways first offset i ways0 with
      | Some args -> Some (s :: args)
      | None -> None)
    | None -> None)

(** val arm_has_table_ways : continuation -> coq_Z -> coq_Z -> table_way list ->
    (coq_Z * apply_cont) -> bool **)

let arm_has_table_ways k first offset ways arm =
  match arguments_by_table_ways first offset (fst arm) ways with
  | Some args ->
    if
      apply_cont_eq_dec (snd arm)
        { ac_continuation = k; ac_args = args; ac_trap_action = None }
    then true
    else false
  | None -> false

(** val table_has_column : coq_Z -> coq_Z -> (coq_Z * simple) list -> (symbol *
    simple list) -> bool **)

let table_has_column first offset column table =
  Nat.eqb (length (snd table)) (length column)
  &&
  let immediates = all_immediates (snd table) in
  forallb
    (fun entry ->
      match table_element first offset (snd table) (fst entry) with
      | Some element ->
        element_taken immediates element
        && if simple_eq_dec (snd entry) element then true else false
      | None -> false)
    column

(** val table_way_of_column : known_tables -> coq_Z -> coq_Z -> (coq_Z * simple)
    list -> table_way option **)

let table_way_of_column tables first offset column =
  match way_of_column column with
  | Some way -> Some (Without_table way)
  | None -> (
    match find (table_has_column first offset column) tables with
    | Some p ->
      let s, elements = p in
      Some (From_table (s, elements, all_immediates elements))
    | None -> None)

(** val table_ways_of_arguments : known_tables -> coq_Z -> coq_Z -> nat ->
    (coq_Z * simple list) list -> table_way list option **)

let rec table_ways_of_arguments tables first offset count rows =
  match count with
  | O -> Some []
  | S count0 -> (
    match column_of_arms rows with
    | Some column -> (
      match table_way_of_column tables first offset column with
      | Some way -> (
        match
          table_ways_of_arguments tables first offset count0 (rest_of_arms rows)
        with
        | Some ways -> Some (way :: ways)
        | None -> None)
      | None -> None)
    | None -> None)

(** val bind_table_load_to : variable -> variable -> symbol -> coq_Z -> coq_Z ->
    bool -> expr -> expr **)

let bind_table_load_to v x s first offset immediates body =
  bind_tagged_to v x
    (bind_table_offset x first offset
       (Let
          ( x,
            Value,
            Prim
              ( Binary
                  (Array_load
                     ( table_array_kind immediates,
                       table_load_kind immediates,
                       Immutable )),
                [Symbol s; Var x] ),
            body )))

(** val bind_table_way : coq_Z -> coq_Z -> variable -> variable -> table_way ->
    expr -> expr **)

let bind_table_way first offset v x way body =
  match way with
  | Without_table way0 -> (
    match way0 with
    | Same_in_every_arm _ -> body
    | Computed how -> bind_way how v x body)
  | From_table (s, _, immediates) ->
    bind_table_load_to v x s first offset immediates body

(** val bind_table_ways : coq_Z -> coq_Z -> variable -> variable list ->
    table_way list -> expr -> expr **)

let rec bind_table_ways first offset v names ways body =
  match names with
  | [] -> body
  | x :: names0 -> (
    match ways with
    | [] -> body
    | way :: ways0 ->
      bind_table_way first offset v x way
        (bind_table_ways first offset v names0 ways0 body))

(** val merged_by_table_way : variable -> variable -> table_way -> simple **)

let merged_by_table_way v x = function
  | Without_table way0 -> (
    match way0 with
    | Same_in_every_arm s -> s
    | Computed how -> ( match how with As_it_is -> Var v | _ -> Var x))
  | From_table (_, _, _) -> Var x

(** val merged_by_table_ways : variable -> variable list -> table_way list ->
    simple list **)

let rec merged_by_table_ways v names ways =
  match names with
  | [] -> []
  | x :: names0 -> (
    match ways with
    | [] -> []
    | way :: ways0 ->
      merged_by_table_way v x way :: merged_by_table_ways v names0 ways0)

(** val table_names_usable : variable -> variable list -> table_way list -> bool
    **)

let table_names_usable v names ways =
  ((Nat.eqb (length names) (length ways) && distinct names)
  && negb (among v names))
  && forallb
       (fun way ->
         match way with
         | Without_table way0 -> (
           match way0 with
           | Same_in_every_arm s ->
             negb (existsb (fun x -> var_in_simple x s) names)
           | Computed _ -> true)
         | From_table (_, _, _) -> true)
       ways

(** val merge_switch_by_table_ways : known_continuations -> known_tables ->
    simple -> (coq_Z * apply_cont) list -> expr option **)

let merge_switch_by_table_ways known tables scrutinee arms =
  match scrutinee with
  | Var v -> (
    match arms with
    | [] -> None
    | p :: l -> (
      let first, ac = p in
      match l with
      | [] -> None
      | _ :: l0 -> (
        match l0 with
        | [] -> None
        | _ :: _ -> (
          let k = ac.ac_continuation in
          match lookup k known with
          | Some names -> (
            let offset = table_offset first in
            match
              table_ways_of_arguments tables first offset (length ac.ac_args)
                (map (fun arm -> fst arm, (snd arm).ac_args) arms)
            with
            | Some ways ->
              if
                (existsb is_from_table ways && table_names_usable v names ways)
                && forallb (arm_has_table_ways k first offset ways) arms
              then
                Some
                  (bind_table_ways first offset v names ways
                     (Apply_cont
                        { ac_continuation = k;
                          ac_args = merged_by_table_ways v names ways;
                          ac_trap_action = None
                        }))
              else None
            | None -> None)
          | None -> None))))
  | _ -> None

(** val merge_switch_with_tables : known_continuations -> known_tables -> simple
    -> (coq_Z * apply_cont) list -> expr **)

let merge_switch_with_tables known tables scrutinee arms =
  match tables with
  | [] -> Switch (scrutinee, arms)
  | _ :: _ -> (
    match merge_switch_by_table tables scrutinee arms with
    | Some merged -> (
      match merge_switch scrutinee arms with
      | Switch (_, _) -> merged
      | _ -> Switch (scrutinee, arms))
    | None -> (
      match merge_switch_by_table_ways known tables scrutinee arms with
      | Some merged -> merged
      | None -> Switch (scrutinee, arms)))

(** val merge_tables_under : known_continuations -> known_tables -> expr -> expr
    **)

let rec merge_tables_under known tables e =
  match e with
  | Let (x, kind, d, body) ->
    Let (x, kind, d, merge_tables_under known tables body)
  | Let_static (bindings, body) ->
    Let_static
      ( bindings,
        merge_tables_under known (tables_under_statics tables bindings) body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        merge_tables_in_handler known tables h,
        merge_tables_under ((k, parameters_of_handler h) :: known) tables body
      )
  | Let_cont_recursive (handlers, body) ->
    let known0 =
      app
        (map
           (fun entry -> fst entry, parameters_of_handler (snd entry))
           handlers)
        known
    in
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, merge_tables_in_handler known0 tables h)
          handlers,
        merge_tables_under known0 tables body )
  | Switch (scrutinee, arms) ->
    merge_switch_with_tables known tables scrutinee arms
  | _ -> e

(** val merge_tables_in_handler : known_continuations -> known_tables ->
    continuation_handler -> continuation_handler **)

and merge_tables_in_handler known tables = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, merge_tables_under known tables handler)

(** val merge_tables_knowing : known_tables -> expr -> expr **)

let merge_tables_knowing tables e = merge_tables_under [] tables e

(** val merge_tables_in_code : known_tables -> expr -> expr **)

let rec merge_tables_in_code tables e =
  match e with
  | Let (x, kind, d, body) -> Let (x, kind, d, merge_tables_in_code tables body)
  | Let_static (bindings, body) ->
    let tables0 = tables_under_statics tables bindings in
    Let_static
      ( map (rewrite_code_in_binding (merge_tables_knowing tables0)) bindings,
        merge_tables_in_code tables0 body )
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        merge_tables_in_code_in_handler tables h,
        merge_tables_in_code tables body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive
      ( map
          (fun pat ->
            let k, h = pat in
            k, merge_tables_in_code_in_handler tables h)
          handlers,
        merge_tables_in_code tables body )
  | _ -> e

(** val merge_tables_in_code_in_handler : known_tables -> continuation_handler
    -> continuation_handler **)

and merge_tables_in_code_in_handler tables = function
  | Handler (params, metadata, handler) ->
    Handler (params, metadata, merge_tables_in_code tables handler)

(** val merge_tables : expr -> expr **)

let merge_tables e = merge_tables_in_code [] (merge_tables_knowing [] e)
