(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)

(* Checks Simplify against the Rocq semantics of Flambda 2 on one example.

   An [.fl] file is parsed to a Flambda unit, which Simplify then rewrites. The
   unit before and the unit after are each converted to a term of the Rocq model
   (middle_end/flambda2/rocq/FlambdaModel.v) and run on the machine extracted
   from FlambdaSemanticsSpec.v. What the two runs come to is printed and
   compared: Simplify is right on the example if, unless the run before is
   undefined, the run after ends the same way.

   This is a test and not a proof. What is trusted, beyond the semantics itself:
   the conversion below, which must be read against the model; and the meaning
   given here to the primitives, which the model leaves abstract ([eval_prim]).
   A construct or a primitive the conversion does not know is reported as
   unsupported, and never run as if it were undefined, as that would make the
   check pass for nothing. *)

(* The matches below name the few constructs and primitives the model has and
   send every other to [unsupported]; they are meant to stay as they are when
   the compiler gains a constructor. *)
[@@@ocaml.warning "-4"]

open Import
open Flambda2_kinds
open Flambda2_numbers
open Flambda2_bound_identifiers
open Flambda2_term_basics
module Model = Flambda2_rocq_semantics.FlambdaModel
module Semantics = Flambda2_rocq_semantics.FlambdaSemanticsSpec
module Numbers = Flambda2_rocq_semantics.BinNums
module P = Flambda_primitive

exception Unsupported of string

let unsupported fmt = Format.kasprintf (fun msg -> raise (Unsupported msg)) fmt

(* ---- Numbers ---------------------------------------------------------- *)

let rec positive_of_int n : Numbers.positive =
  if n <= 1
  then Coq_xH
  else if n land 1 = 0
  then Coq_xO (positive_of_int (n lsr 1))
  else Coq_xI (positive_of_int (n lsr 1))

let z_of_int n : Numbers.coq_Z =
  if n = 0
  then Z0
  else if n > 0
  then Zpos (positive_of_int n)
  else Zneg (positive_of_int (-n))

let rec int_of_positive (p : Numbers.positive) =
  match p with
  | Coq_xH -> 1
  | Coq_xO p -> 2 * int_of_positive p
  | Coq_xI p -> (2 * int_of_positive p) + 1

let int_of_z (z : Numbers.coq_Z) =
  match z with
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> -int_of_positive p

(* ---- Names ------------------------------------------------------------ *)

(* Each sort of name of the compiler is numbered from 1 as it is met. The names
   the compiler gives when it opens a binder are fresh, so a name stands for one
   thing throughout a unit. *)
module Numbering (Id : sig
  type t

  val compare : t -> t -> int
end) =
struct
  module Map = Map.Make (Id)

  let numbers = ref Map.empty

  let next = ref 1

  let find id =
    match Map.find_opt id !numbers with
    | Some n -> positive_of_int n
    | None ->
      let n = !next in
      incr next;
      numbers := Map.add id n !numbers;
      positive_of_int n
end

module Variables = Numbering (Variable)
module Continuations = Numbering (Continuation)
module Symbols = Numbering (Symbol)
module Code_ids = Numbering (Code_id)
module Value_slots = Numbering (Value_slot)

(* ---- Primitives ------------------------------------------------------- *)

(* The primitives the tool gives a meaning to. Integers are the tagged and the
   naked immediates, with OCaml's own arithmetic on [int], which is that of the
   target on 64 bits. *)
type prim =
  | Unary of P.unary_primitive
  | Binary of P.binary_primitive

let supported_int_kind (kind : Flambda_kind.Standard_int.t) =
  match kind with
  | Tagged_immediate | Naked_immediate -> true
  | Naked_int8 | Naked_int16 | Naked_int32 | Naked_int64 | Naked_nativeint ->
    false

let check_supported (p : prim) =
  match p with
  | Unary (Tag_immediate | Untag_immediate | Is_int _ | Opaque_identity _) -> ()
  | Binary (Int_arith (kind, (Add | Sub | Mul | And | Or | Xor)))
    when supported_int_kind kind ->
    ()
  | Binary (Int_comp (kind, Yielding_bool _)) when supported_int_kind kind -> ()
  | Unary p ->
    let zero = Simple.const_zero Sixty_four in
    unsupported "primitive %a" P.print (P.Unary (p, zero))
  | Binary p ->
    let zero = Simple.const_zero Sixty_four in
    unsupported "primitive %a" P.print (P.Binary (p, zero, zero))

let int_of_value (kind : Flambda_kind.Standard_int.t) (v : Semantics.value) =
  match kind, v with
  | Tagged_immediate, Value_const (Tagged_immediate i)
  | Naked_immediate, Value_const (Naked_immediate i) ->
    Some (int_of_z i)
  | _, _ -> None

let value_of_int (kind : Flambda_kind.Standard_int.t) i : Semantics.value option
    =
  match kind with
  | Tagged_immediate -> Some (Value_const (Tagged_immediate (z_of_int i)))
  | Naked_immediate -> Some (Value_const (Naked_immediate (z_of_int i)))
  | Naked_int8 | Naked_int16 | Naked_int32 | Naked_int64 | Naked_nativeint ->
    None

let naked_bool b : Semantics.value =
  Value_const (Naked_immediate (z_of_int (if b then 1 else 0)))

let compare_ints (cmp : P.signed_or_unsigned P.comparison) a b =
  let unsigned_compare a b = compare (a - min_int) (b - min_int) in
  let ordering (signedness : P.signed_or_unsigned) =
    match signedness with
    | Signed -> compare a b
    | Unsigned -> unsigned_compare a b
  in
  match cmp with
  | Eq -> a = b
  | Neq -> a <> b
  | Lt s -> ordering s < 0
  | Gt s -> ordering s > 0
  | Le s -> ordering s <= 0
  | Ge s -> ordering s >= 0

let eval_prim (p : prim) (args : Semantics.value list) : Semantics.value option
    =
  match p, args with
  | Unary Tag_immediate, [Value_const (Naked_immediate i)] ->
    Some (Value_const (Tagged_immediate i))
  | Unary Untag_immediate, [Value_const (Tagged_immediate i)] ->
    Some (Value_const (Naked_immediate i))
  | Unary (Is_int _), [v] ->
    Some
      (naked_bool
         (match v with
         | Value_const (Tagged_immediate _) -> true
         | Value_const _ | Value_closure _ | Value_symbol _ -> false))
  | Unary (Opaque_identity _), [v] -> Some v
  | Binary (Int_arith (kind, op)), [a; b] -> (
    match int_of_value kind a, int_of_value kind b with
    | Some a, Some b -> (
      match op with
      | Add -> value_of_int kind (a + b)
      | Sub -> value_of_int kind (a - b)
      | Mul -> value_of_int kind (a * b)
      | And -> value_of_int kind (a land b)
      | Or -> value_of_int kind (a lor b)
      | Xor -> value_of_int kind (a lxor b)
      | Div _ | Mod _ -> None)
    | _, _ -> None)
  | Binary (Int_comp (kind, Yielding_bool cmp)), [a; b] -> (
    match int_of_value kind a, int_of_value kind b with
    | Some a, Some b -> Some (naked_bool (compare_ints cmp a b))
    | _, _ -> None)
  | _, _ -> None

let () =
  Flambda2_rocq_semantics.Prim_hook.eval_prim
    := fun p args -> Obj.repr (eval_prim (Obj.obj p) (Obj.obj args))

(* ---- Conversion of terms ---------------------------------------------- *)

let convert_const (c : Reg_width_const.t) : Model.const =
  match Reg_width_const.descr c with
  | Naked_immediate i -> Naked_immediate (z_of_int (Target_ocaml_int.to_int i))
  | Tagged_immediate i ->
    Tagged_immediate (z_of_int (Target_ocaml_int.to_int i))
  | Null -> Null
  | Naked_float32 _ | Naked_float _ | Naked_int8 _ | Naked_int16 _
  | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _ | Naked_vec128 _
  | Naked_vec256 _ | Naked_vec512 _ | Naked_mask _ | Poison _ ->
    unsupported "constant %a" Reg_width_const.print c

let convert_simple (s : Simple.t) : Model.simple =
  Simple.pattern_match' s
    ~var:(fun var ~coercion:_ -> Model.Var (Variables.find var))
    ~symbol:(fun symbol ~coercion:_ -> Model.Symbol (Symbols.find symbol))
    ~const:(fun c -> Model.Const (convert_const c))

let convert_simples = List.map convert_simple

let convert_value_slots (slots : Simple.t Value_slot.Map.t) =
  Value_slot.Map.bindings slots
  |> List.map (fun (slot, s) -> Value_slots.find slot, convert_simple s)

(* A set of closures of one function. *)
let convert_set_of_closures (set : Set_of_closures.t) =
  let funs =
    Function_declarations.funs_in_order (Set_of_closures.function_decls set)
  in
  match Function_slot.Lmap.bindings funs with
  | [ ( _,
        (Code_id { code_id; _ } :
          Function_declarations.code_id_in_function_declaration) ) ] ->
    Code_ids.find code_id, convert_value_slots (Set_of_closures.value_slots set)
  | [(_, Deleted _)] -> unsupported "a closure of deleted code"
  | [] | _ :: _ :: _ -> unsupported "a set of closures of several functions"

let convert_apply_cont (ac : Apply_cont_expr.t) : Model.apply_cont =
  (match Apply_cont_expr.trap_action ac with
  | None -> ()
  | Some _ -> unsupported "a trap action");
  { ac_continuation = Continuations.find (Apply_cont_expr.continuation ac);
    ac_args = convert_simples (Apply_cont_expr.args ac)
  }

let convert_params (params : Bound_parameters.t) =
  List.map Variables.find (Bound_parameters.vars params)

let rec convert_expr (e : Flambda.Expr.t) : Model.expr =
  match Flambda.Expr.descr e with
  | Let let_expr ->
    Flambda.Let_expr.pattern_match let_expr ~f:(fun pattern ~body ->
        convert_let pattern (Flambda.Let_expr.defining_expr let_expr) body)
  | Let_cont (Non_recursive { handler; _ }) ->
    Flambda.Non_recursive_let_cont_handler.pattern_match handler
      ~f:(fun k ~body ->
        let handler =
          convert_handler ~invariant_params:[]
            (Flambda.Non_recursive_let_cont_handler.handler handler)
        in
        Model.Let_cont_non_recursive
          (Continuations.find k, handler, convert_expr body))
  | Let_cont (Recursive handlers) ->
    Flambda.Recursive_let_cont_handlers.pattern_match handlers
      ~f:(fun ~invariant_params ~body handlers ->
        let invariant_params = convert_params invariant_params in
        let handlers =
          Flambda.Continuation_handlers.to_map handlers
          |> Continuation.Lmap.bindings
          |> List.map (fun (k, handler) ->
              Continuations.find k, convert_handler ~invariant_params handler)
        in
        Model.Let_cont_recursive (handlers, convert_expr body))
  | Apply apply -> Model.Apply (convert_apply apply)
  | Apply_cont ac -> Model.Apply_cont (convert_apply_cont ac)
  | Switch switch ->
    let arms =
      Target_ocaml_int.Map.bindings (Switch_expr.arms switch)
      |> List.map (fun (discriminant, arm) ->
          ( z_of_int (Target_ocaml_int.to_int discriminant),
            convert_apply_cont (Switch_arm.action arm) ))
    in
    Model.Switch (convert_simple (Switch_expr.scrutinee switch), arms)
  | Invalid _ -> Model.Invalid

and convert_handler ~invariant_params (handler : Flambda.Continuation_handler.t)
    : Model.continuation_handler =
  Flambda.Continuation_handler.pattern_match handler ~f:(fun params ~handler ->
      Model.Handler
        (invariant_params @ convert_params params, convert_expr handler))

and convert_let (pattern : Bound_pattern.t) (defining_expr : Flambda.Named.t)
    body : Model.expr =
  match pattern, defining_expr with
  | Singleton bound_var, Simple s ->
    Model.Let
      ( Variables.find (Bound_var.var bound_var),
        Simple (convert_simple s),
        convert_expr body )
  | Singleton bound_var, Prim (prim, _) ->
    Model.Let
      ( Variables.find (Bound_var.var bound_var),
        convert_prim prim,
        convert_expr body )
  | Set_of_closures [bound_var], Set_of_closures (set, _) ->
    let code, slots = convert_set_of_closures set in
    Model.Let
      ( Variables.find (Bound_var.var bound_var),
        Set_of_closures (code, slots),
        convert_expr body )
  | Static bound_static, Static_consts group ->
    let bindings =
      Flambda.Static_const_group.match_against_bound_static group bound_static
        ~init:[]
        ~code:(fun bindings code_id code ->
          Model.Bind_code (Code_ids.find code_id, convert_code code) :: bindings)
        ~deleted_code:(fun bindings code_id ->
          Model.Bind_deleted_code (Code_ids.find code_id) :: bindings)
        ~set_of_closures:(fun bindings ~closure_symbols set ->
          match Function_slot.Lmap.bindings closure_symbols with
          | [(_, symbol)] ->
            let code, slots = convert_set_of_closures set in
            Model.Bind_symbol
              (Symbols.find symbol, Static_const_set_of_closures (code, slots))
            :: bindings
          | [] | _ :: _ :: _ ->
            unsupported "a set of closures of several functions")
        ~block_like:(fun bindings symbol const ->
          Model.Bind_symbol (Symbols.find symbol, convert_static_const const)
          :: bindings)
    in
    Model.Let_static (List.rev bindings, convert_expr body)
  | Singleton _, (Set_of_closures _ | Static_consts _ | Rec_info _)
  | Set_of_closures _, _
  | Static _, _ ->
    unsupported "the binding %a" Bound_pattern.print pattern

and convert_prim (prim : P.t) : Model.named =
  match prim with
  | Unary (Project_value_slot { value_slot; _ }, closure) ->
    Project_value_slot (Value_slots.find value_slot, convert_simple closure)
  | Unary (p, arg) ->
    check_supported (Unary p);
    Prim (Obj.repr (Unary p), [convert_simple arg])
  | Binary (p, arg1, arg2) ->
    check_supported (Binary p);
    Prim (Obj.repr (Binary p), [convert_simple arg1; convert_simple arg2])
  | Nullary _ | Ternary _ | Quaternary _ | Variadic _ ->
    unsupported "primitive %a" P.print prim

and convert_static_const (const : Static_const.t) : Model.static_const =
  match const with
  | Block (tag, Immutable, _, fields) ->
    Static_const_block
      ( z_of_int (Tag.Scannable.to_int tag),
        List.map
          (fun field -> convert_simple (Simple.With_debuginfo.simple field))
          fields )
  | Immutable_string s ->
    Static_const_immutable_string
      (List.init (String.length s) (fun i -> z_of_int (Char.code s.[i])))
  | _ -> unsupported "static constant %a" Static_const.print const

and convert_code (code : Flambda.Function_params_and_body.t Code0.t) :
    Model.code =
  Flambda.Function_params_and_body.pattern_match (Code0.params_and_body code)
    ~f:(fun
        ~return_continuation
        ~exn_continuation
        params
        ~body
        ~my_closure
        ~is_my_closure_used:_
        ~my_alloc_mode:_
        ~my_depth:_
        ~free_names_of_body:_
      ->
      Model.Code
        ( convert_params params,
          Variables.find my_closure,
          Continuations.find return_continuation,
          Continuations.find exn_continuation,
          convert_expr body ))

and convert_apply (apply : Apply_expr.t) : Model.apply_expr =
  let callee =
    match Apply_expr.callee apply with
    | Some callee -> convert_simple callee
    | None -> unsupported "a call with no callee"
  in
  let call_kind : Model.call_kind =
    match Apply_expr.call_kind apply with
    | Function { function_call = Direct code_id; _ } ->
      Direct (Code_ids.find code_id)
    | Function
        { function_call = Indirect_unknown_arity | Indirect_known_arity _; _ }
      ->
      Indirect
    | Method _ | C_call _ | Effect _ ->
      unsupported "the call %a" Apply_expr.print apply
  in
  let continuation =
    match Apply_expr.continuation apply with
    | Return k -> Continuations.find k
    | Never_returns -> unsupported "a call that never returns"
  in
  let exn_continuation = Apply_expr.exn_continuation apply in
  (match Exn_continuation.extra_args exn_continuation with
  | [] -> ()
  | _ :: _ -> unsupported "extra arguments to an exception continuation");
  { ap_callee = callee;
    ap_call_kind = call_kind;
    ap_args = convert_simples (Apply_expr.args apply);
    ap_continuation = continuation;
    ap_exn_continuation =
      Continuations.find (Exn_continuation.exn_handler exn_continuation)
  }

(* ---- Running ---------------------------------------------------------- *)

(* What is observed of a value: what it is, through the symbols it points to. A
   closure is not looked into: its code differs before and after. *)
type observation =
  | Tagged of int
  | Naked of string * int
  | Null
  | Block of int * observation list
  | Boxed of observation
  | String of string
  | Function
  | Dangling
  | Too_deep

let rec observe depth (statics : Semantics.static_env) (v : Semantics.value) :
    observation =
  if depth = 0
  then Too_deep
  else
    match v with
    | Value_const (Tagged_immediate i) -> Tagged (int_of_z i)
    | Value_const (Naked_immediate i) -> Naked ("imm", int_of_z i)
    | Value_const Null -> Null
    | Value_const _ -> Naked ("number", 0)
    | Value_closure _ -> Function
    | Value_symbol symbol -> (
      match Semantics.lookup symbol statics.static_values with
      | None -> Dangling
      | Some (Static_closure _) -> Function
      | Some (Static_block (tag, fields)) ->
        Block (int_of_z tag, List.map (observe (depth - 1) statics) fields)
      | Some (Static_boxed_number v) -> Boxed (observe (depth - 1) statics v)
      | Some (Static_string bytes) ->
        String
          (String.init (List.length bytes) (fun i ->
               Char.chr (int_of_z (List.nth bytes i)))))

let rec print_observation ppf (o : observation) =
  match o with
  | Tagged i -> Format.fprintf ppf "%d" i
  | Naked (kind, i) -> Format.fprintf ppf "#%d:%s" i kind
  | Null -> Format.fprintf ppf "null"
  | Block (tag, fields) ->
    Format.fprintf ppf "@[<hov 1>[%d:@ %a]@]" tag
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ";@ ")
         print_observation)
      fields
  | Boxed o -> Format.fprintf ppf "@[<hov 1>(boxed@ %a)@]" print_observation o
  | String s -> Format.fprintf ppf "%S" s
  | Function -> Format.fprintf ppf "<fun>"
  | Dangling -> Format.fprintf ppf "<unbound symbol>"
  | Too_deep -> Format.fprintf ppf "..."

type outcome =
  | Returns of observation list
  | Raises of observation list
  | Exits_elsewhere
  | Undefined
  | Still_running

let print_outcome ppf (outcome : outcome) =
  let print_values ppf values =
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
      print_observation ppf values
  in
  match outcome with
  | Returns values ->
    Format.fprintf ppf "@[<hov 2>returns@ %a@]" print_values values
  | Raises values ->
    Format.fprintf ppf "@[<hov 2>raises@ %a@]" print_values values
  | Exits_elsewhere -> Format.fprintf ppf "applies an unbound continuation"
  | Undefined -> Format.fprintf ppf "undefined"
  | Still_running -> Format.fprintf ppf "still running when the fuel ran out"

let fuel = 1_000_000

(* The calls that are not in code: those of the unit itself, which inlining
   removes. *)
let rec calls_outside_code (e : Model.expr) =
  let in_handler (Model.Handler (_, handler)) = calls_outside_code handler in
  match e with
  | Let (_, _, body) | Let_static (_, body) -> calls_outside_code body
  | Let_cont_non_recursive (_, handler, body) ->
    in_handler handler + calls_outside_code body
  | Let_cont_recursive (handlers, body) ->
    List.fold_left
      (fun calls (_, handler) -> calls + in_handler handler)
      (calls_outside_code body) handlers
  | Apply _ -> 1
  | Apply_cont _ | Switch _ | Invalid -> 0

let run (unit : Flambda_unit.t) : outcome * int * int =
  let body = convert_expr (Flambda_unit.body unit) in
  let return_continuation =
    Continuations.find (Flambda_unit.return_continuation unit)
  in
  let exn_continuation =
    Continuations.find (Flambda_unit.exn_continuation unit)
  in
  let rec go steps (state : Semantics.state) =
    if steps >= fuel
    then Still_running, steps, calls_outside_code body
    else
      match Semantics.step state with
      | Step state -> go (steps + 1) state
      | Undefined -> Undefined, steps, calls_outside_code body
      | Exit (k, values) ->
        let (State (_, _, _, statics)) = state in
        let values = List.map (observe 50 statics) values in
        ( (if k = return_continuation
           then Returns values
           else if k = exn_continuation
           then Raises values
           else Exits_elsewhere),
          steps,
          calls_outside_code body )
  in
  go 0 (State (body, [], [], Semantics.empty_static_env))

(* ---- The check -------------------------------------------------------- *)

let check ~filename (before : Flambda_unit.t) (after : Flambda_unit.t) =
  match run before, run after with
  | exception Unsupported what ->
    Format.printf "%s: not checked: the model has not got %s@." filename what
  | (before, steps_before, calls_before), (after, steps_after, calls_after) ->
    Format.printf "%s:@.  before Simplify (%d steps): %a@." filename
      steps_before print_outcome before;
    Format.printf "  after Simplify (%d steps): %a@." steps_after print_outcome
      after;
    Format.printf "  calls outside code: %d before, %d after@." calls_before
      calls_after;
    let verdict, ok =
      match before, after with
      | Undefined, _ -> "anything goes, as the run before is undefined", true
      | Still_running, _ | _, Still_running -> "not decided", true
      | _, _ -> if before = after then "the same", true else "DIFFERENT", false
    in
    Format.printf "  %s@." verdict;
    if not ok then exit 1

let check_file filename =
  match Parse_flambda.parse_fexpr filename with
  | Error e ->
    Test_utils.dump_error e;
    exit 1
  | Ok unit ->
    let unit_info = Parse_flambda.make_unit_info ~filename in
    let comp_unit = Unit_info.modname unit_info in
    Env.set_current_unit unit_info;
    let fl2 = Fexpr_to_flambda.conv comp_unit unit in
    let null_formatter =
      Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
    in
    let result =
      Flambda2.flambda_to_flambda ~ppf_dump:null_formatter
        ~prefixname:(Filename.chop_extension filename)
        ~machine_width:Sixty_four ~code_slot_offsets:fl2.code_slot_offsets
        fl2.unit
    in
    check ~filename:(Filename.basename filename) fl2.unit result.flambda

module Options = Oxcaml_args.Make_optcomp_options (Oxcaml_args.Default.Optmain)

let () =
  Clflags.set_target Clflags.Target.Native;
  let files = ref [] in
  let defer_file file =
    match Filename.extension file with
    | ".fl" -> files := file :: !files
    | ext -> Misc.fatal_errorf "Unrecognized extension %s" ext
  in
  Compenv.warnings_for_discarded_params := true;
  Compenv.set_extra_params (Some Oxcaml_args.Extra_params.read_param);
  Compenv.readenv Format.err_formatter Before_args;
  Clflags.add_arguments __LOC__ (Arch.command_line_options @ Options.list);
  Clflags.Opt_flag_handler.set Oxcaml_flags.opt_flag_handler;
  Compenv.parse_arguments (ref Sys.argv) defer_file "flsemantics";
  Location.read_clflags_from_env ();
  List.iter check_file (List.rev !files)
