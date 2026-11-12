open BinInt
open BinNums
open BinPos
open FlambdaCseSpec
open FlambdaKindModel
open FlambdaModel
open FlambdaPrimitiveModel

(** val first_known : ((variable * (prim * simple list)) -> 'a1 option) ->
    computed -> 'a1 option **)

let rec first_known f = function
  | [] -> None
  | entry :: known0 -> (
    match f entry with Some a -> Some a | None -> first_known f known0)

type comparison = (standard_int * signedness) * simple list

(** val comparison_held : variable -> (variable * (prim * simple list)) ->
    comparison option **)

let comparison_held u = function
  | y, p -> (
    let p0, operands = p in
    match p0 with
    | Binary p1 -> (
      match p1 with
      | Int_comp (kind, behaviour) -> (
        match behaviour with
        | Yielding_bool _ -> None
        | Yielding_int_like_compare_functions s ->
          if Pos.eqb u y then Some ((kind, s), operands) else None)
      | _ -> None)
    | _ -> None)

(** val tagged_comparison_held : computed -> variable -> (variable * (prim *
    simple list)) -> comparison option **)

let tagged_comparison_held known t = function
  | y, p -> (
    let p0, l = p in
    match p0 with
    | Unary p1 -> (
      match p1 with
      | Tag_immediate -> (
        match l with
        | [] -> None
        | s :: l0 -> (
          match s with
          | Var u -> (
            match l0 with
            | [] ->
              if Pos.eqb t y
              then first_known (comparison_held u) known
              else None
            | _ :: _ -> None)
          | _ -> None))
      | _ -> None)
    | _ -> None)

(** val compared : computed -> simple -> comparison option **)

let compared known = function
  | Var t -> first_known (tagged_comparison_held known t) known
  | _ -> None

(** val is_tagged_zero : simple -> bool **)

let is_tagged_zero = function
  | Const c -> ( match c with Tagged_immediate i -> Z.eqb i Z0 | _ -> false)
  | _ -> false

(** val tested : prim -> int_comparison option **)

let tested = function
  | Binary p0 -> (
    match p0 with
    | Phys_equal op -> (
      match op with Phys_eq -> Some Int_eq | Phys_neq -> Some Int_neq)
    | Int_comp (kind, behaviour) -> (
      match kind with
      | Standard_tagged_immediate -> (
        match behaviour with
        | Yielding_bool c -> Some c
        | Yielding_int_like_compare_functions _ -> None)
      | _ -> None)
    | _ -> None)
  | _ -> None

(** val swap_comparison : int_comparison -> int_comparison **)

let swap_comparison = function
  | Int_lt s -> Int_gt s
  | Int_gt s -> Int_lt s
  | Int_le s -> Int_ge s
  | Int_ge s -> Int_le s
  | x -> x

(** val against_zero : signedness -> int_comparison -> int_comparison option **)

let against_zero s = function
  | Int_lt s0 -> ( match s0 with Signed -> Some (Int_lt s) | Unsigned -> None)
  | Int_gt s0 -> (
    match s0 with Signed -> Some (Int_gt s) | Unsigned -> Some Int_neq)
  | Int_le s0 -> (
    match s0 with Signed -> Some (Int_le s) | Unsigned -> Some Int_eq)
  | Int_ge s0 -> ( match s0 with Signed -> Some (Int_ge s) | Unsigned -> None)
  | x -> Some x

(** val recover_one_way : computed -> simple -> simple -> int_comparison ->
    named option **)

let recover_one_way known tagged zero c =
  if is_tagged_zero zero
  then
    match compared known tagged with
    | Some c0 -> (
      let p, operands = c0 in
      let kind, s = p in
      match against_zero s c with
      | Some c' ->
        Some (Prim (Binary (Int_comp (kind, Yielding_bool c')), operands))
      | None -> None)
    | None -> None
  else None

(** val recover_comparison : computed -> named -> named **)

let recover_comparison known d =
  match d with
  | Prim (p, args) -> (
    match args with
    | [] -> d
    | arg1 :: l -> (
      match l with
      | [] -> d
      | arg2 :: l0 -> (
        match l0 with
        | [] -> (
          match tested p with
          | Some c -> (
            match recover_one_way known arg1 arg2 c with
            | Some d' -> d'
            | None -> (
              match recover_one_way known arg2 arg1 (swap_comparison c) with
              | Some d' -> d'
              | None -> d))
          | None -> d)
        | _ :: _ -> d)))
  | _ -> d

(** val recover_comparisons_knowing : computed -> expr -> expr **)

let rec recover_comparisons_knowing known e =
  match e with
  | Let (x, kind, d, body) ->
    Let
      ( x,
        kind,
        recover_comparison known d,
        recover_comparisons_knowing (computed_under_let known x d) body )
  | Let_static (bindings, body) ->
    Let_static (bindings, recover_comparisons_knowing known body)
  | Let_cont_non_recursive (k, h, body) ->
    Let_cont_non_recursive
      ( k,
        recover_comparisons_in_handler known h,
        recover_comparisons_knowing known body )
  | Let_cont_recursive (handlers, body) ->
    Let_cont_recursive (handlers, recover_comparisons_knowing known body)
  | _ -> e

(** val recover_comparisons_in_handler : computed -> continuation_handler ->
    continuation_handler **)

and recover_comparisons_in_handler known = function
  | Handler (params, metadata, handler) ->
    Handler
      ( params,
        metadata,
        recover_comparisons_knowing (forget_computed_vars params known) handler
      )

(** val recover_known_comparisons : expr -> expr **)

let recover_known_comparisons e = recover_comparisons_knowing [] e
