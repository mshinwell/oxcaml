open NaturalLoop
open SsaDominance
open SsaGraph
open SsaModel

(** val is_loop_invariant : op_def -> block -> value -> bool **)

let is_loop_invariant op_def0 header0 v =
  match Ssa_view.value v with
  | Res (id, op, _) -> (
    match op with
    | Operation.Const_int _ -> true
    | Operation.Const_float32 _ -> true
    | Operation.Const_float _ -> true
    | Operation.Const_symbol _ -> true
    | Operation.Const_vec128 _ -> true
    | Operation.Const_vec256 _ -> true
    | Operation.Const_vec512 _ -> true
    | Operation.Const_mask _ -> true
    | _ -> (
      match Ssa.Instruction.Id.Tbl.find_opt op_def0 id with
      | Some bl -> strictly_dominates bl header0
      | None -> false))
  | Block_param (block0, _) -> strictly_dominates block0 header0

type biv_step =
  | Step_const of int
  | Step_var of value

type biv =
  { loop : natural_loop;
    param_index : int;
    update : value list;
    step : biv_step;
    sign : [`Add | `Sub]
  }

(** val step_same : biv_step -> biv_step -> bool **)

let step_same a b =
  match a with
  | Step_const x -> (
    match b with Step_const y -> Int.equal x y | Step_var _ -> false)
  | Step_var x -> (
    match b with Step_const _ -> false | Step_var y -> Ssa.Value.equal x y)

(** val sign_same : [ `Add | `Sub ] -> [ `Add | `Sub ] -> bool **)

let sign_same a b =
  match a with
  | `Add -> ( match b with `Add -> true | `Sub -> false)
  | `Sub -> ( match b with `Add -> false | `Sub -> true)

(** val signed_step : biv -> int option **)

let signed_step biv0 =
  match biv0.step with
  | Step_const c -> (
    match biv0.sign with
    | `Add -> Some c
    | `Sub -> if Int.equal c Int.min_int then None else Some (Int.neg c))
  | Step_var _ -> None

(** val classify_update : (value -> bool) -> op_def -> block -> value ->
    (biv_step * [ `Add | `Sub ]) option **)

let classify_update is_self op_def0 header0 v =
  match Ssa_view.value v with
  | Res (_, op, args) -> (
    match op with
    | Operation.Intop op0 -> (
      match op0 with
      | Operation.Iadd -> (
        match args with
        | [] -> None
        | x :: l -> (
          match l with
          | [] -> None
          | y :: l0 -> (
            match l0 with
            | [] ->
              if is_self x && is_loop_invariant op_def0 header0 y
              then Some (Step_var y, `Add)
              else if is_self y && is_loop_invariant op_def0 header0 x
              then Some (Step_var x, `Add)
              else None
            | _ :: _ -> None)))
      | Operation.Isub -> (
        match args with
        | [] -> None
        | x :: l -> (
          match l with
          | [] -> None
          | y :: l0 -> (
            match l0 with
            | [] ->
              if is_self x && is_loop_invariant op_def0 header0 y
              then Some (Step_var y, `Sub)
              else None
            | _ :: _ -> None)))
      | _ -> None)
    | Operation.Intop_imm (op0, c) -> (
      match op0 with
      | Operation.Iadd -> (
        match args with
        | [] -> None
        | x :: l -> (
          match l with
          | [] -> if is_self x then Some (Step_const c, `Add) else None
          | _ :: _ -> None))
      | Operation.Isub -> (
        match args with
        | [] -> None
        | x :: l -> (
          match l with
          | [] -> if is_self x then Some (Step_const c, `Sub) else None
          | _ :: _ -> None))
      | _ -> None)
    | _ -> None)
  | Block_param (_, _) -> None

(** val back_edge_set : natural_loop -> blockset **)

let back_edge_set loop0 =
  List.fold_left
    (fun s b -> Ssa.Block.Set.add b s)
    Ssa.Block.Set.empty loop0.back_edges

(** val classify_param : natural_loop -> op_def -> (block * Ssa.finished
    Ssa.Terminator.arg list) list -> int -> biv option **)

let classify_param loop0 op_def0 back_pred_args index =
  let is_self = is_param loop0.header index in
  let back_vals_opt =
    List.map
      (fun pat ->
        let _, args = pat in
        arg_value args index)
      back_pred_args
  in
  if List.for_all Option.is_some back_vals_opt
  then
    let back_vals = List.filter_map (fun v -> v) back_vals_opt in
    match back_vals with
    | [] -> None
    | first :: rest -> (
      match classify_update is_self op_def0 loop0.header first with
      | Some p ->
        let step0, sign0 = p in
        let agrees =
          List.for_all
            (fun v ->
              match classify_update is_self op_def0 loop0.header v with
              | Some p0 ->
                let step', sign' = p0 in
                step_same step0 step' && sign_same sign0 sign'
              | None -> false)
            rest
        in
        if agrees
        then
          Some
            { loop = loop0;
              param_index = index;
              update = back_vals;
              step = step0;
              sign = sign0
            }
        else None
      | None -> None)
  else None

(** val params_bivs : natural_loop -> op_def -> (block * Ssa.finished
    Ssa.Terminator.arg list) list -> int -> value list -> biv list **)

let rec params_bivs loop0 op_def0 back_pred_args index = function
  | [] -> []
  | _ :: params0 -> (
    let rest = params_bivs loop0 op_def0 back_pred_args (index + 1) params0 in
    match classify_param loop0 op_def0 back_pred_args index with
    | Some biv0 -> biv0 :: rest
    | None -> rest)

(** val analyze_loop : op_def -> natural_loop -> biv list **)

let analyze_loop op_def0 loop0 =
  let header0 = loop0.header in
  let back_set = back_edge_set loop0 in
  let pred_args =
    List.map (fun p -> p, goto_args header0 p) (Ssa.Block.predecessors header0)
  in
  let all_back_edges_have_args =
    List.for_all
      (fun pat ->
        let p, args = pat in
        (not (Ssa.Block.Set.mem p back_set)) || Option.is_some args)
      pred_args
  in
  if not all_back_edges_have_args
  then []
  else
    let back_pred_args =
      List.filter_map
        (fun pat ->
          let p, args = pat in
          if Ssa.Block.Set.mem p back_set
          then Option.map (fun args0 -> p, args0) args
          else None)
        pred_args
    in
    params_bivs loop0 op_def0 back_pred_args 0 (Ssa_view.params header0)

(** val analyze : op_def -> block list -> (natural_loop * biv list) list **)

let analyze op_def0 blocks =
  List.map (fun loop0 -> loop0, analyze_loop op_def0 loop0) (find_loops blocks)
