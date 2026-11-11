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
module Compare = Flambda2_rocq_semantics.FlambdaCompareSpec
module Normalise = Flambda2_rocq_semantics.FlambdaNormaliseSpec
module Aliases = Flambda2_rocq_semantics.FlambdaAliasesSpec
module Unused_statics = Flambda2_rocq_semantics.FlambdaUnusedStaticsSpec
module Well_formed = Flambda2_rocq_semantics.FlambdaWellFormedSpec
module Numbers = Flambda2_rocq_semantics.BinNums
module P = Flambda_primitive

exception Unsupported of (Format.formatter -> unit)

let unsupported fmt = Format.kdprintf (fun msg -> raise (Unsupported msg)) fmt

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

  (* Gives [id] the number of [same_as]. *)
  let alias id ~same_as =
    ignore (find same_as : Numbers.positive);
    numbers := Map.add id (Map.find same_as !numbers) !numbers
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

(* Structural equality decides the equality of [prim]: the primitives that
   [check_supported] lets through hold only constant constructors and kinds. *)
let () =
  Flambda2_rocq_semantics.Prim_hook.prim_eqb
    := fun p p' -> (Obj.obj p : prim) = (Obj.obj p' : prim)

(* Everything is folded but [Opaque_identity], whose point is that the
   simplifier does not look through it. *)
let () =
  Flambda2_rocq_semantics.Prim_hook.prim_may_fold
    := fun p ->
         match (Obj.obj p : prim) with
         | Unary (Opaque_identity _) -> false
         | Unary _ | Binary _ -> true

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

(* The code that is a newer version of other code, with that code, and the code
   that is bound as deleted, noted as a unit is converted. *)
let newer_versions : (Code_id.t * Code_id.t) list ref = ref []

let deleted_code : Code_id.t list ref = ref []

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
          (match Code0.newer_version_of code with
          | Some older -> newer_versions := (code_id, older) :: !newer_versions
          | None -> ());
          Model.Bind_code (Code_ids.find code_id, convert_code code) :: bindings)
        ~deleted_code:(fun bindings code_id ->
          deleted_code := code_id :: !deleted_code;
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

type converted =
  { body : Model.expr;
    return_continuation : Model.continuation;
    exn_continuation : Model.continuation
  }

let convert_unit (unit : Flambda_unit.t) : converted =
  { body = convert_expr (Flambda_unit.body unit);
    return_continuation =
      Continuations.find (Flambda_unit.return_continuation unit);
    exn_continuation = Continuations.find (Flambda_unit.exn_continuation unit)
  }

let run (unit : converted) : outcome * int =
  let rec go steps (state : Semantics.state) =
    if steps >= fuel
    then Still_running, steps
    else
      match Semantics.step state with
      | Step state -> go (steps + 1) state
      | Undefined -> Undefined, steps
      | Exit (k, values) ->
        let (State (_, _, _, statics)) = state in
        let values = List.map (observe 50 statics) values in
        ( (if k = unit.return_continuation
           then Returns values
           else if k = unit.exn_continuation
           then Raises values
           else Exits_elsewhere),
          steps )
  in
  go 0 (State (unit.body, [], [], Semantics.empty_static_env))

(* ---- Printing model terms ---------------------------------------------- *)

(* For looking at what the normalisation made of the two terms, when an example
   is not validated (set FLSEMANTICS_PRINT_TERMS). *)
let print_list print ppf items =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
    print ppf items

let print_var ppf x = Format.fprintf ppf "v%d" (int_of_positive x)

let print_simple ppf (s : Model.simple) =
  match s with
  | Var x -> print_var ppf x
  | Symbol sym -> Format.fprintf ppf "$%d" (int_of_positive sym)
  | Const (Tagged_immediate i) -> Format.fprintf ppf "%d" (int_of_z i)
  | Const (Naked_immediate i) -> Format.fprintf ppf "#%d" (int_of_z i)
  | Const Null -> Format.fprintf ppf "null"
  | Const _ -> Format.fprintf ppf "<const>"

let print_simples = print_list print_simple

let print_cont ppf k = Format.fprintf ppf "k%d" (int_of_positive k)

let print_value_slots ppf slots =
  print_list
    (fun ppf (slot, s) ->
      Format.fprintf ppf "%d = %a" (int_of_positive slot) print_simple s)
    ppf slots

let print_prim ppf (p : Model.prim) =
  match (Obj.obj p : prim) with
  | Unary p -> P.Without_args.print ppf (Unary p)
  | Binary p -> P.Without_args.print ppf (Binary p)

let print_named ppf (d : Model.named) =
  match d with
  | Simple s -> print_simple ppf s
  | Prim (p, args) ->
    Format.fprintf ppf "@[<hov 2>%a@ (%a)@]" print_prim p print_simples args
  | Set_of_closures (code, slots) ->
    Format.fprintf ppf "@[<hov 2>closure code%d@ {%a}@]" (int_of_positive code)
      print_value_slots slots
  | Project_value_slot (slot, closure) ->
    Format.fprintf ppf "%a.slot%d" print_simple closure (int_of_positive slot)

let print_apply_cont ppf (ac : Model.apply_cont) =
  Format.fprintf ppf "@[<hov 2>cont %a@ (%a)@]" print_cont ac.ac_continuation
    print_simples ac.ac_args

let rec print_expr ppf (e : Model.expr) =
  match e with
  | Let (x, d, body) ->
    Format.fprintf ppf "@[<hov 2>let %a =@ %a in@]@ %a" print_var x print_named
      d print_expr body
  | Let_static (bindings, body) ->
    Format.fprintf ppf "@[<v 2>let static@ %a@]@ in@ %a"
      (Format.pp_print_list print_binding)
      bindings print_expr body
  | Let_cont_non_recursive (k, handler, body) ->
    Format.fprintf ppf "@[<v 2>let_cont %a %a@]@ in@ %a" print_cont k
      print_handler handler print_expr body
  | Let_cont_recursive (handlers, body) ->
    Format.fprintf ppf "@[<v 2>let_cont rec@ %a@]@ in@ %a"
      (Format.pp_print_list (fun ppf (k, handler) ->
           Format.fprintf ppf "%a %a" print_cont k print_handler handler))
      handlers print_expr body
  | Apply ap ->
    Format.fprintf ppf "@[<hov 2>apply%s %a@ (%a)@ -> %a * %a@]"
      (match ap.ap_call_kind with
      | Direct code -> Printf.sprintf " direct(code%d)" (int_of_positive code)
      | Indirect -> "")
      print_simple ap.ap_callee print_simples ap.ap_args print_cont
      ap.ap_continuation print_cont ap.ap_exn_continuation
  | Apply_cont ac -> print_apply_cont ppf ac
  | Switch (scrutinee, arms) ->
    Format.fprintf ppf "@[<v 2>switch %a@ %a@]" print_simple scrutinee
      (Format.pp_print_list (fun ppf (i, ac) ->
           Format.fprintf ppf "| %d -> %a" (int_of_z i) print_apply_cont ac))
      arms
  | Invalid -> Format.fprintf ppf "invalid"

and print_handler ppf (Model.Handler (params, handler)) =
  Format.fprintf ppf "(%a) =@ @[<v>%a@]" (print_list print_var) params
    print_expr handler

and print_binding ppf (binding : Model.static_binding) =
  match binding with
  | Bind_code (id, Code (params, my_closure, ret, exn, body)) ->
    Format.fprintf ppf "@[<v 2>code%d (%a) %a -> %a * %a =@ %a@]"
      (int_of_positive id) (print_list print_var) params print_var my_closure
      print_cont ret print_cont exn print_expr body
  | Bind_deleted_code id ->
    Format.fprintf ppf "code%d deleted" (int_of_positive id)
  | Bind_symbol (sym, Static_const_set_of_closures (code, slots)) ->
    Format.fprintf ppf "@[<hov 2>$%d = closure code%d@ {%a}@]"
      (int_of_positive sym) (int_of_positive code) print_value_slots slots
  | Bind_symbol (sym, Static_const_block (tag, fields)) ->
    Format.fprintf ppf "@[<hov 2>$%d = Block %d@ (%a)@]" (int_of_positive sym)
      (int_of_z tag) print_simples fields
  | Bind_symbol (sym, Static_const_boxed_number contents) ->
    Format.fprintf ppf "$%d = boxed %a" (int_of_positive sym) print_simple
      contents
  | Bind_symbol (sym, Static_const_immutable_string _) ->
    Format.fprintf ppf "$%d = <string>" (int_of_positive sym)

(* ---- Static bindings that are not used --------------------------------- *)

(* The symbols and code ids that a term binds and that nothing live refers to:
   not the term outside its static bindings, and not a static binding that is
   itself live. This is only a guess of what may be removed:
   FlambdaUnusedStaticsSpec.drop_statics checks it before removing anything. *)
type static_name =
  | Symbol_name of Model.symbol
  | Code_name of Model.code_id

let unused_statics (e : Model.expr) : Unused_statics.dropped =
  (* What each binding refers to, and what the term refers to outside its
     bindings ([None]). *)
  let references : (static_name option * static_name) list ref = ref [] in
  let bound : static_name list ref = ref [] in
  let refer owner name = references := (owner, name) :: !references in
  let in_simple owner (s : Model.simple) =
    match s with
    | Symbol sym -> refer owner (Symbol_name sym)
    | Var _ | Const _ -> ()
  in
  let in_simples owner = List.iter (in_simple owner) in
  let in_slots owner = List.iter (fun (_, s) -> in_simple owner s) in
  let rec in_expr owner (e : Model.expr) =
    match e with
    | Let (_, d, body) ->
      (match d with
      | Simple s | Project_value_slot (_, s) -> in_simple owner s
      | Prim (_, args) -> in_simples owner args
      | Set_of_closures (code, slots) ->
        refer owner (Code_name code);
        in_slots owner slots);
      in_expr owner body
    | Let_static (bindings, body) ->
      List.iter
        (fun (binding : Model.static_binding) ->
          match binding with
          | Bind_code (id, Code (_, _, _, _, code_body)) ->
            bound := Code_name id :: !bound;
            in_expr (Some (Code_name id)) code_body
          | Bind_deleted_code _ -> ()
          | Bind_symbol (sym, const) -> (
            bound := Symbol_name sym :: !bound;
            let owner = Some (Symbol_name sym) in
            match const with
            | Static_const_set_of_closures (code, slots) ->
              refer owner (Code_name code);
              in_slots owner slots
            | Static_const_block (_, fields) -> in_simples owner fields
            | Static_const_boxed_number contents -> in_simple owner contents
            | Static_const_immutable_string _ -> ()))
        bindings;
      in_expr owner body
    | Let_cont_non_recursive (_, Handler (_, handler), body) ->
      in_expr owner handler;
      in_expr owner body
    | Let_cont_recursive (handlers, body) ->
      List.iter
        (fun (_, Model.Handler (_, handler)) -> in_expr owner handler)
        handlers;
      in_expr owner body
    | Apply ap -> (
      in_simple owner ap.ap_callee;
      in_simples owner ap.ap_args;
      match ap.ap_call_kind with
      | Direct code -> refer owner (Code_name code)
      | Indirect -> ())
    | Apply_cont ac -> in_simples owner ac.ac_args
    | Switch (scrutinee, arms) ->
      in_simple owner scrutinee;
      List.iter
        (fun (_, (ac : Model.apply_cont)) -> in_simples owner ac.ac_args)
        arms
    | Invalid -> ()
  in
  in_expr None e;
  let rec live_from live =
    let live' =
      List.fold_left
        (fun live (owner, name) ->
          let owner_is_live =
            match owner with None -> true | Some owner -> List.mem owner live
          in
          if owner_is_live && not (List.mem name live)
          then name :: live
          else live)
        live !references
    in
    if List.length live' = List.length live then live else live_from live'
  in
  let live = live_from [] in
  let unused = List.filter (fun name -> not (List.mem name live)) !bound in
  { dropped_symbols =
      List.filter_map
        (function Symbol_name sym -> Some sym | Code_name _ -> None)
        unused;
    dropped_code =
      List.filter_map
        (function Code_name id -> Some id | Symbol_name _ -> None)
        unused
  }

(* ---- The check -------------------------------------------------------- *)

(* Whether a code id is used: called, made a closure of, or bound to code. Being
   bound as deleted is not a use. *)
let rec code_id_used (id : Model.code_id) (e : Model.expr) =
  let in_handler (Model.Handler (_, handler)) = code_id_used id handler in
  let in_binding (binding : Model.static_binding) =
    match binding with
    | Bind_code (bound, Code (_, _, _, _, body)) ->
      bound = id || code_id_used id body
    | Bind_deleted_code _ -> false
    | Bind_symbol (_, Static_const_set_of_closures (code, _)) -> code = id
    | Bind_symbol
        ( _,
          ( Static_const_block _ | Static_const_boxed_number _
          | Static_const_immutable_string _ ) ) ->
      false
  in
  match e with
  | Let (_, Set_of_closures (code, _), body) ->
    code = id || code_id_used id body
  | Let (_, (Simple _ | Prim _ | Project_value_slot _), body) ->
    code_id_used id body
  | Let_static (bindings, body) ->
    List.exists in_binding bindings || code_id_used id body
  | Let_cont_non_recursive (_, handler, body) ->
    in_handler handler || code_id_used id body
  | Let_cont_recursive (handlers, body) ->
    List.exists (fun (_, handler) -> in_handler handler) handlers
    || code_id_used id body
  | Apply { ap_call_kind = Direct code; _ } -> code = id
  | Apply { ap_call_kind = Indirect; _ } | Apply_cont _ | Switch _ | Invalid ->
    false

(* The two units are converted with one numbering of names, the continuations of
   the second unit standing for those of the first, so that the verified
   comparison can be made of the two bodies as they are.

   Simplify gives a new code id to each new version of a piece of code, and
   binds the old one as deleted. The comparison wants code ids to be the same,
   so the new id is given the number of the old where that changes nothing:
   where the unit after binds the old one as deleted and does not otherwise use
   it. The unit after is converted once to find that out, and again with the
   numbers settled.

   CR mshinwell: This identification is part of what is trusted, and will most
   likely not be enough: it does nothing for code that has no older version, or
   whose older version is still used. The comparison should relate code ids
   itself; see the CR in middle_end/flambda2/rocq/FlambdaCompareSpec.v for what
   that takes. *)
let convert_both (before : Flambda_unit.t) (after : Flambda_unit.t) =
  let before_converted = convert_unit before in
  Continuations.alias
    (Flambda_unit.return_continuation after)
    ~same_as:(Flambda_unit.return_continuation before);
  Continuations.alias
    (Flambda_unit.exn_continuation after)
    ~same_as:(Flambda_unit.exn_continuation before);
  newer_versions := [];
  deleted_code := [];
  let first_pass = convert_unit after in
  List.iter
    (fun (newer, older) ->
      if
        List.exists (Code_id.equal older) !deleted_code
        && not (code_id_used (Code_ids.find older) first_pass.body)
      then Code_ids.alias newer ~same_as:older)
    !newer_versions;
  before_converted, convert_unit after

(* Static bindings at toplevel only, each name bound once
   (FlambdaWellFormedSpec.v). *)
let well_formed (unit : converted) =
  Well_formed.well_formed_unit unit.exn_continuation unit.body

(* The term before is checked before Simplify sees it, which is entitled to fail
   on one that is not well-formed. *)
let well_formed_before ~filename (before : Flambda_unit.t) =
  match convert_unit before with
  | exception Unsupported _ -> true
  | before ->
    let ok = well_formed before in
    if not ok
    then
      Format.printf
        "%s: not checked: the term is not well-formed (a static binding that \
         is not at toplevel, or a name bound twice)@."
        filename;
    ok

let check ~filename (before : Flambda_unit.t) (after : Flambda_unit.t) =
  match convert_both before after with
  | exception Unsupported what ->
    Format.printf "%s: not checked: the model has not got %s@." filename
      (Format.asprintf "%t" what)
  | _, after when not (well_formed after) ->
    Format.printf "%s: the term after Simplify is NOT WELL-FORMED@." filename;
    exit 1
  | before, after ->
    let outcome_before, steps_before = run before in
    let outcome_after, steps_after = run after in
    Format.printf "%s:@.  before Simplify (%d steps): %a@." filename
      steps_before print_outcome outcome_before;
    Format.printf "  after Simplify (%d steps): %a@." steps_after print_outcome
      outcome_after;
    Format.printf "  calls outside code: %d before, %d after@."
      (calls_outside_code before.body)
      (calls_outside_code after.body);
    let verdict, ok =
      match outcome_before, outcome_after with
      | Undefined, _ -> "anything goes, as the run before is undefined", true
      | Still_running, _ | _, Still_running -> "not decided", true
      | _, _ ->
        if outcome_before = outcome_after
        then "the same", true
        else "DIFFERENT", false
    in
    Format.printf "  %s@." verdict;
    (* What the test above shows of one run, this shows of all. The term before
       is normalised by rewrites proved to refine it: calls of known code are
       inlined, constants are folded, a continuation applied once at the end of
       its scope is put there, and unused bindings are removed
       (FlambdaNormaliseSpec.v); aliases are followed (FlambdaAliasesSpec.v).
       The term after may only be rewritten to what is equivalent: its aliases
       are followed, its constants folded and its bindings of deleted code
       dropped. The two are then the same up to bound names, which is proved to
       make them equivalent (FlambdaCompareSpec.v). *)
    let inlined = Normalise.inline_calls [] before.body in
    Format.printf
      "  calls outside code once those of known code are inlined: %d@."
      (calls_outside_code inlined);
    (* The rewrites enable one another, so they are gone round a few times. Each
       is proved, whatever the order and the number. *)
    let rec rounds n round term =
      let term' = round term in
      if n = 0 || term' = term then term' else rounds (n - 1) round term'
    in
    let normalised_before =
      rounds 50
        (fun term ->
          Normalise.inline_calls [] term
          |> Normalise.fold_constants |> Normalise.collapse_switches
          |> Normalise.inline_tail_conts |> Aliases.follow_aliases []
          |> Normalise.fold_constants |> Normalise.remove_unused_lets
          |> Normalise.remove_unused_defined_lets []
          |> Normalise.drop_deleted_code |> Normalise.merge_statics)
        before.body
    in
    let normalised_after =
      rounds 50
        (fun term ->
          Aliases.follow_aliases [] term
          |> Normalise.inline_known_calls [] []
          |> Normalise.fold_constants
          |> Normalise.remove_unused_defined_lets []
          |> Normalise.drop_deleted_code |> Normalise.merge_statics)
        after.body
    in
    let validated_as_is = Compare.expr_eqb [] [] before.body after.body in
    let validated =
      validated_as_is
      || Compare.expr_eqb [] [] normalised_before normalised_after
    in
    (* Failing that, the static bindings of the term before that nothing uses
       are removed, which is proved to refine it for a term run on its own and
       not under every environment (FlambdaUnusedStaticsSpec.v), and the
       comparison made again. *)
    let without_unused_statics =
      match
        Unused_statics.drop_statics
          (unused_statics normalised_before)
          normalised_before
      with
      | Some dropped ->
        Normalise.merge_statics (Normalise.drop_deleted_code dropped)
      | None -> normalised_before
    in
    let validated_as_a_unit =
      (not validated)
      && Compare.expr_eqb [] [] without_unused_statics normalised_after
    in
    Format.printf "  %s@."
      (if validated_as_is
       then "validated: the same up to bound names"
       else if validated
       then "validated: the same once normalised"
       else if validated_as_a_unit
       then
         "validated for the unit run on its own: the same once normalised and \
          unused static bindings removed"
       else if outcome_before = Undefined
       then "nothing to validate, as the term before is undefined"
       else "not validated");
    if
      (not validated) && (not validated_as_a_unit)
      && Sys.getenv_opt "FLSEMANTICS_PRINT_TERMS" <> None
    then
      Format.printf
        "@[<v 2>  the term before, normalised:@ %a@]@.@[<v 2>  the term after, \
         normalised:@ %a@]@."
        print_expr without_unused_statics print_expr normalised_after;
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
    let filename_shown = Filename.basename filename in
    if well_formed_before ~filename:filename_shown fl2.unit
    then
      let null_formatter =
        Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
      in
      let result =
        Flambda2.flambda_to_flambda ~ppf_dump:null_formatter
          ~prefixname:(Filename.chop_extension filename)
          ~machine_width:Sixty_four ~code_slot_offsets:fl2.code_slot_offsets
          fl2.unit
      in
      check ~filename:filename_shown fl2.unit result.flambda

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
