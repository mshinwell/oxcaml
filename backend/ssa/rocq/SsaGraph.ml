open OxCamlList
open SsaModel

(** val terminator_pure_control : Ssa.finished Ssa.Terminator.t -> bool **)

let terminator_pure_control t =
  (fun f_continue
    f_switch
    f_call
    f_invalid
    (t : Ssa.finished Ssa.Terminator.t)
  ->
    match t with
    | Ssa.Terminator.Continue { continuation; args } ->
      f_continue continuation (Array.to_list args)
    | Ssa.Terminator.Switch { index; targets } ->
      f_switch index (Array.to_list targets)
    | Ssa.Terminator.Call { args; _ } -> f_call (Array.to_list args)
    | Ssa.Terminator.Invalid { args; _ } -> f_invalid (Array.to_list args))
    (fun continuation _ ->
      match continuation with Ssa.Goto _ -> true | _ -> false)
    (fun _ _ -> true)
    (fun _ -> false)
    (fun _ -> false)
    t

(** val block_effect_free : block -> bool **)

let block_effect_free bl =
  List.for_all
    (fun i -> not (Ssa.Instruction.has_side_effect i))
    (block_body bl)
  && terminator_pure_control (Ssa.Block.terminator bl)

(** val is_param : block -> int -> Ssa.finished Ssa.Value.t -> bool **)

let is_param bl index v = Ssa.Value.equal v (Ssa.Block.param bl index)

(** val instr_defines_value : Ssa.finished Ssa.Instruction.t -> Ssa.finished
    Ssa.Value.t -> bool **)

let instr_defines_value i v =
  (fun f_op f_push_trap f_pop_trap (i : Ssa.finished Ssa.Instruction.t) ->
    match i with
    | Ssa.Instruction.Op { Ssa.Instruction.id; args; _ } ->
      f_op id (Array.to_list args)
    | Ssa.Instruction.Push_trap _ -> f_push_trap ()
    | Ssa.Instruction.Pop_trap _ -> f_pop_trap ())
    (fun id _ ->
      (fun f_res f_param (v : Ssa.finished Ssa.Value.t) ->
        match v with
        | Ssa.Instruction.Res ({ Ssa.Instruction.id; op; args; _ }, i) ->
          f_res id op (Array.to_list args) i
        | Ssa.Instruction.Block_param (b, i) -> f_param b i)
        (fun id' _ _ _ -> Ssa.Instruction.Id.equal id id')
        (fun _ _ -> false)
        v)
    (fun _ -> false)
    (fun _ -> false)
    i

(** val args_of_instr : Ssa.finished Ssa.Instruction.t -> Ssa.finished
    Ssa.Value.t list **)

let args_of_instr i =
  (fun f_op f_push_trap f_pop_trap (i : Ssa.finished Ssa.Instruction.t) ->
    match i with
    | Ssa.Instruction.Op { Ssa.Instruction.id; args; _ } ->
      f_op id (Array.to_list args)
    | Ssa.Instruction.Push_trap _ -> f_push_trap ()
    | Ssa.Instruction.Pop_trap _ -> f_pop_trap ())
    (fun _ args -> args)
    (fun _ -> [])
    (fun _ -> [])
    i

(** val terminator_args : Ssa.finished Ssa.Terminator.t -> Ssa.finished
    Ssa.Value.t list list **)

let terminator_args term =
  (fun f_continue
    f_switch
    f_call
    f_invalid
    (t : Ssa.finished Ssa.Terminator.t)
  ->
    match t with
    | Ssa.Terminator.Continue { continuation; args } ->
      f_continue continuation (Array.to_list args)
    | Ssa.Terminator.Switch { index; targets } ->
      f_switch index (Array.to_list targets)
    | Ssa.Terminator.Call { args; _ } -> f_call (Array.to_list args)
    | Ssa.Terminator.Invalid { args; _ } -> f_invalid (Array.to_list args))
    (fun _ args ->
      List.filter_map
        (fun arg ->
          match arg with
          | Ssa.Terminator.Arg v -> Some v
          | Ssa.Terminator.Omitted_since_unused -> None)
        args
      :: [])
    (fun index _ -> (index :: []) :: [])
    (fun args -> args :: [])
    (fun args -> args :: [])
    term

(** val arg_is : Ssa.finished Ssa.Value.t -> Ssa.finished Ssa.Terminator.arg ->
    bool **)

let arg_is v = function
  | Ssa.Terminator.Arg a -> Ssa.Value.equal a v
  | Ssa.Terminator.Omitted_since_unused -> false

(** val arg_value : Ssa.finished Ssa.Terminator.arg list -> int -> Ssa.finished
    Ssa.Value.t option **)

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
  (fun f_continue
    f_switch
    f_call
    f_invalid
    (t : Ssa.finished Ssa.Terminator.t)
  ->
    match t with
    | Ssa.Terminator.Continue { continuation; args } ->
      f_continue continuation (Array.to_list args)
    | Ssa.Terminator.Switch { index; targets } ->
      f_switch index (Array.to_list targets)
    | Ssa.Terminator.Call { args; _ } -> f_call (Array.to_list args)
    | Ssa.Terminator.Invalid { args; _ } -> f_invalid (Array.to_list args))
    (fun continuation args ->
      match continuation with
      | Ssa.Goto goto ->
        if Ssa.Block.equal goto target && same_length args (params target)
        then Some args
        else None
      | _ -> None)
    (fun _ _ -> None)
    (fun _ -> None)
    (fun _ -> None)
    (Ssa.Block.terminator pred)

(** val goto_passes : block -> int -> Ssa.finished Ssa.Value.t -> block -> bool
    **)

let goto_passes target k v bl =
  (fun f_continue
    f_switch
    f_call
    f_invalid
    (t : Ssa.finished Ssa.Terminator.t)
  ->
    match t with
    | Ssa.Terminator.Continue { continuation; args } ->
      f_continue continuation (Array.to_list args)
    | Ssa.Terminator.Switch { index; targets } ->
      f_switch index (Array.to_list targets)
    | Ssa.Terminator.Call { args; _ } -> f_call (Array.to_list args)
    | Ssa.Terminator.Invalid { args; _ } -> f_invalid (Array.to_list args))
    (fun continuation args ->
      match continuation with
      | Ssa.Goto goto ->
        (Ssa.Block.equal goto target
        &&
        match arg_value args k with
        | Some a -> Ssa.Value.equal a v
        | None -> false)
        && Int.equal (count_occurrences (arg_is v) args) 1
      | _ -> false)
    (fun _ _ -> false)
    (fun _ -> false)
    (fun _ -> false)
    (Ssa.Block.terminator bl)

(** val all_uses_ok : block list -> (Ssa.finished Ssa.Value.t -> bool) ->
    (Ssa.finished Ssa.Instruction.t -> bool) -> (block -> Ssa.finished
    Ssa.Value.t list -> bool) -> bool **)

let all_uses_ok blocks same approve_instr approve_term =
  List.for_all
    (fun bl ->
      List.for_all
        (fun i -> (not (List.exists same (args_of_instr i))) || approve_instr i)
        (block_body bl)
      && List.for_all
           (fun arr -> (not (List.exists same arr)) || approve_term bl arr)
           (terminator_args (Ssa.Block.terminator bl)))
    blocks

(** val visit_all : (blockset -> block -> blockset option) -> blockset -> block
    list -> blockset option **)

let rec visit_all visit seen = function
  | [] -> Some seen
  | b :: roots0 -> (
    match visit seen b with
    | Some seen0 -> visit_all visit seen0 roots0
    | None -> None)

(** val visit_acyclic : block list -> blockset -> block -> blockset -> blockset
    -> block -> blockset option **)

let rec visit_acyclic fuel region cut active seen b =
  if
    (Ssa.Block.equal b cut || not (Ssa.Block.Set.mem b region))
    || Ssa.Block.Set.mem b seen
  then Some seen
  else if Ssa.Block.Set.mem b active
  then None
  else
    match fuel with
    | [] -> None
    | _ :: fuel0 -> (
      match
        visit_all
          (visit_acyclic fuel0 region cut (Ssa.Block.Set.add b active))
          seen
          (Ssa.Block.all_successors b)
      with
      | Some seen0 -> Some (Ssa.Block.Set.add b seen0)
      | None -> None)

(** val acyclic_except : block list -> blockset -> block -> bool **)

let acyclic_except blocks region cut =
  match
    visit_all
      (visit_acyclic blocks region cut Ssa.Block.Set.empty)
      Ssa.Block.Set.empty blocks
  with
  | Some seen ->
    Ssa.Block.Set.for_all
      (fun b -> Ssa.Block.equal b cut || Ssa.Block.Set.mem b seen)
      region
  | None -> false
