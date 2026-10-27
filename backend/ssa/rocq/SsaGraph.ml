open OxCamlList
open SsaModel

(** val terminator_pure_control : Terminator.t -> bool **)

let terminator_pure_control = function
  | Terminator.Continue (continuation, _) -> (
    match continuation with Ssa.Goto _ -> true | _ -> false)
  | Terminator.Switch (_, _) -> true
  | _ -> false

(** val block_effect_free : block -> bool **)

let block_effect_free bl =
  List.for_all
    (fun i -> not (Ssa.Instruction.has_side_effect i))
    (Ssa_view.body bl)
  && terminator_pure_control (Ssa_view.terminator bl)

(** val is_param : block -> int -> value -> bool **)

let is_param bl index v = Ssa.Value.equal v (Ssa.Block.param bl index)

(** val instr_defines_value : instr -> value -> bool **)

let instr_defines_value i v =
  match Ssa_view.instr i with
  | Op (id, _) -> (
    match Ssa_view.value v with
    | Res (id', _) -> Ssa.Instruction.Id.equal id id'
    | Block_param (_, _) -> false)
  | _ -> false

(** val args_of_instr : instr -> value list **)

let args_of_instr i =
  match Ssa_view.instr i with Op (_, args) -> args | _ -> []

(** val terminator_args : Terminator.t -> value list list **)

let terminator_args = function
  | Terminator.Continue (_, args) ->
    List.filter_map
      (fun arg ->
        match arg with
        | Ssa.Terminator.Arg v -> Some v
        | Ssa.Terminator.Omitted_since_unused -> None)
      args
    :: []
  | Terminator.Switch (index, _) -> (index :: []) :: []
  | Terminator.Call args -> args :: []
  | Terminator.Invalid args -> args :: []

(** val arg_is : value -> Ssa.finished Ssa.Terminator.arg -> bool **)

let arg_is v = function
  | Ssa.Terminator.Arg a -> Ssa.Value.equal a v
  | Ssa.Terminator.Omitted_since_unused -> false

(** val arg_value : Ssa.finished Ssa.Terminator.arg list -> int -> value option
    **)

let arg_value args index =
  match nth_int args index with
  | Some a -> (
    match a with
    | Ssa.Terminator.Arg v -> Some v
    | Ssa.Terminator.Omitted_since_unused -> None)
  | None -> None

(** val goto_args : block -> block -> Ssa.finished Ssa.Terminator.arg list
    option **)

let goto_args target pred =
  match Ssa_view.terminator pred with
  | Terminator.Continue (continuation, args) -> (
    match continuation with
    | Ssa.Goto goto ->
      if
        Ssa.Block.equal goto target && same_length args (Ssa_view.params target)
      then Some args
      else None
    | _ -> None)
  | _ -> None

(** val goto_passes : block -> int -> value -> block -> bool **)

let goto_passes target k v bl =
  match Ssa_view.terminator bl with
  | Terminator.Continue (continuation, args) -> (
    match continuation with
    | Ssa.Goto goto ->
      (Ssa.Block.equal goto target
      &&
      match arg_value args k with
      | Some a -> Ssa.Value.equal a v
      | None -> false)
      && Int.equal (count_occurrences (arg_is v) args) 1
    | _ -> false)
  | _ -> false

(** val all_uses_ok : block list -> (value -> bool) -> (instr -> bool) -> (block
    -> value list -> bool) -> bool **)

let all_uses_ok blocks same approve_instr approve_term =
  List.for_all
    (fun bl ->
      List.for_all
        (fun i -> (not (List.exists same (args_of_instr i))) || approve_instr i)
        (Ssa_view.body bl)
      && List.for_all
           (fun arr -> (not (List.exists same arr)) || approve_term bl arr)
           (terminator_args (Ssa_view.terminator bl)))
    blocks
