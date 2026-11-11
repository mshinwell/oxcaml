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
   the conversion below, which must be read against the model. What a primitive
   computes is the model's to say (FlambdaPrimitiveSpec.v); the conversion only
   says which primitive of the model stands for one of the compiler's. A
   construct or a primitive the conversion does not know is reported as
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
module Maps = Flambda2_rocq_semantics.FlambdaMapSpec
module Kinds = Flambda2_rocq_semantics.FlambdaKindModel
module Primitives = Flambda2_rocq_semantics.FlambdaPrimitiveModel
module Model = Flambda2_rocq_semantics.FlambdaModel
module Values = Flambda2_rocq_semantics.FlambdaValueSpec
module Semantics = Flambda2_rocq_semantics.FlambdaSemanticsSpec
module Normalise = Flambda2_rocq_semantics.FlambdaNormaliseSpec
module Unused_statics = Flambda2_rocq_semantics.FlambdaUnusedStaticsSpec
module Well_formed = Flambda2_rocq_semantics.FlambdaWellFormedSpec
module Validate = Flambda2_rocq_semantics.FlambdaValidateSpec
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

let rec nat_of_int n : Flambda2_rocq_semantics.Datatypes.nat =
  if n <= 0 then O else S (nat_of_int (n - 1))

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

(* The integers of 64 bits: a positive number of the model is read as, and
   written from, the unsigned reading of an [int64]. *)
let rec positive_of_int64 n : Numbers.positive =
  if Int64.equal n 1L
  then Coq_xH
  else if Int64.equal (Int64.logand n 1L) 0L
  then Coq_xO (positive_of_int64 (Int64.shift_right_logical n 1))
  else Coq_xI (positive_of_int64 (Int64.shift_right_logical n 1))

let z_of_int64 n : Numbers.coq_Z =
  if Int64.equal n 0L
  then Z0
  else if Int64.compare n 0L > 0
  then Zpos (positive_of_int64 n)
  else Zneg (positive_of_int64 (Int64.neg n))

(* Through [int64], as the opposite of the least [int] is not an [int]. *)
let z_of_int n = z_of_int64 (Int64.of_int n)

let rec int64_of_positive (p : Numbers.positive) =
  match p with
  | Coq_xH -> 1L
  | Coq_xO p -> Int64.mul 2L (int64_of_positive p)
  | Coq_xI p -> Int64.add (Int64.mul 2L (int64_of_positive p)) 1L

let int64_of_z (z : Numbers.coq_Z) =
  match z with
  | Z0 -> 0L
  | Zpos p -> int64_of_positive p
  | Zneg p -> Int64.neg (int64_of_positive p)

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

(* The primitives the model has (FlambdaPrimitiveModel.v), with the fields it
   keeps of each. One that is not there, or that has a field with a value that
   is not there, is unsupported. *)
let convert_kind (kind : Flambda_kind.t) : Kinds.flambda_kind =
  match kind with
  | Value -> Value
  | Naked_number Naked_immediate -> Naked_number Kind_naked_immediate
  | Naked_number Naked_float32 -> Naked_number Kind_naked_float32
  | Naked_number Naked_float -> Naked_number Kind_naked_float
  | Naked_number Naked_int8 -> Naked_number Kind_naked_int8
  | Naked_number Naked_int16 -> Naked_number Kind_naked_int16
  | Naked_number Naked_int32 -> Naked_number Kind_naked_int32
  | Naked_number Naked_int64 -> Naked_number Kind_naked_int64
  | Naked_number Naked_nativeint -> Naked_number Kind_naked_nativeint
  | Naked_number Naked_vec128 -> Naked_number Kind_naked_vec128
  | Naked_number Naked_vec256 -> Naked_number Kind_naked_vec256
  | Naked_number Naked_vec512 -> Naked_number Kind_naked_vec512
  | Naked_number Naked_mask -> Naked_number Kind_naked_mask
  | Region -> Region
  | Rec_info -> Rec_info

let convert_standard_int (kind : Flambda_kind.Standard_int.t) :
    Kinds.standard_int =
  match kind with
  | Tagged_immediate -> Standard_tagged_immediate
  | Naked_immediate -> Standard_naked_immediate
  | Naked_int8 -> Standard_naked_int8
  | Naked_int16 -> Standard_naked_int16
  | Naked_int32 -> Standard_naked_int32
  | Naked_int64 -> Standard_naked_int64
  | Naked_nativeint -> Standard_naked_nativeint

let convert_boxable_number (kind : Flambda_kind.Boxable_number.t) :
    Kinds.boxable_number =
  match kind with
  | Naked_float32 -> Boxable_naked_float32
  | Naked_float -> Boxable_naked_float
  | Naked_int32 -> Boxable_naked_int32
  | Naked_int64 -> Boxable_naked_int64
  | Naked_nativeint -> Boxable_naked_nativeint
  | Naked_vec128 -> Boxable_naked_vec128
  | Naked_vec256 -> Boxable_naked_vec256
  | Naked_vec512 -> Boxable_naked_vec512
  | Naked_mask -> Boxable_naked_mask

let convert_signed_or_unsigned (signedness : P.signed_or_unsigned) :
    Primitives.signedness =
  match signedness with Signed -> Signed | Unsigned -> Unsigned

let convert_signedness (signedness : Scalar.Signedness.t) :
    Primitives.signedness =
  match signedness with Signed -> Signed | Unsigned -> Unsigned

let convert_or_unknown convert (known : _ Flambda2_lattices.Or_unknown.t) =
  match known with Known a -> Some (z_of_int (convert a)) | Unknown -> None

let convert_unary_primitive (p : P.unary_primitive) :
    Primitives.unary_primitive option =
  match p with
  | Block_load
      { kind = Values { tag; size; field_kind }; mut = Immutable; field } ->
    let field_kind : Primitives.block_access_field_kind =
      match field_kind with Any_value -> Any_value | Immediate -> Immediate
    in
    let kind : Primitives.block_access_kind =
      Block_access_values
        ( convert_or_unknown Tag.Scannable.to_int tag,
          convert_or_unknown Target_ocaml_int.to_int size,
          field_kind )
    in
    Some (Block_load (kind, z_of_int (Target_ocaml_int.to_int field)))
  | Block_load _ -> None
  | Is_int { variant_only } -> Some (Is_int variant_only)
  | Is_null -> Some Is_null
  | Get_tag -> Some Get_tag
  | Opaque_identity { middle_end_only = _; kind } ->
    Some (Opaque_identity (convert_kind kind))
  | Unbox_number kind -> Some (Unbox_number (convert_boxable_number kind))
  | Box_number (kind, Heap _) -> Some (Box_number (convert_boxable_number kind))
  | Box_number (_, Local _) -> None
  | Untag_immediate -> Some Untag_immediate
  | Tag_immediate -> Some Tag_immediate
  | _ -> None

let convert_int_arith_op (op : P.binary_int_arith_op) :
    Primitives.binary_int_arith_op =
  match op with
  | Add -> Add
  | Sub -> Sub
  | Mul -> Mul
  | Div signedness -> Div (convert_signedness signedness)
  | Mod signedness -> Mod (convert_signedness signedness)
  | And -> And
  | Or -> Or
  | Xor -> Xor

let convert_int_comparison (cmp : P.signed_or_unsigned P.comparison) :
    Primitives.int_comparison =
  match cmp with
  | Eq -> Int_eq
  | Neq -> Int_neq
  | Lt signedness -> Int_lt (convert_signed_or_unsigned signedness)
  | Gt signedness -> Int_gt (convert_signed_or_unsigned signedness)
  | Le signedness -> Int_le (convert_signed_or_unsigned signedness)
  | Ge signedness -> Int_ge (convert_signed_or_unsigned signedness)

let convert_binary_primitive (p : P.binary_primitive) :
    Primitives.binary_primitive option =
  match p with
  | Int_arith (kind, op) ->
    Some (Int_arith (convert_standard_int kind, convert_int_arith_op op))
  | Int_comp (kind, Yielding_bool cmp) ->
    let behaviour : Primitives.int_comparison_behaviour =
      Yielding_bool (convert_int_comparison cmp)
    in
    Some (Int_comp (convert_standard_int kind, behaviour))
  | Int_comp (kind, Yielding_int_like_compare_functions signedness) ->
    Some
      (Int_comp
         ( convert_standard_int kind,
           Yielding_int_like_compare_functions
             (convert_signed_or_unsigned signedness) ))
  | _ -> None

(* The compiler's [Make_block] carries the kind of each field, one for each
   argument, with its subkind, and Simplify takes an argument that is a variable
   to be of the subkind of its field: where it cannot be, the primitive becomes
   [Invalid] ([Simplify_variadic_primitive]). The model's [Make_block] has no
   such annotation and makes a block of whatever values it is given. So the only
   annotation converted is the one that says nothing, [any_value] for every
   field; a block kind that says more of a field is not in the model. *)
let convert_variadic_primitive (p : P.variadic_primitive) ~num_args :
    Primitives.variadic_primitive option =
  match p with
  | Make_block (Values (tag, kinds), Immutable, Heap _)
    when List.compare_length_with kinds num_args = 0
         && List.for_all
              (fun kind ->
                Flambda_kind.With_subkind.equal kind
                  Flambda_kind.With_subkind.any_value)
              kinds ->
    Some (Make_block (Block_kind_values (z_of_int (Tag.Scannable.to_int tag))))
  | _ -> None

(* ---- Conversion of terms ---------------------------------------------- *)

(* A float is its bit pattern, read as a signed integer. *)
let convert_float32 f : Model.const =
  Naked_float32
    (z_of_int64
       (Int64.of_int32 (Numeric_types.Float32_by_bit_pattern.to_bits f)))

let convert_float f : Model.const =
  Naked_float (z_of_int64 (Numeric_types.Float_by_bit_pattern.to_bits f))

let convert_const (c : Reg_width_const.t) : Model.const =
  match Reg_width_const.descr c with
  | Naked_immediate i -> Naked_immediate (z_of_int (Target_ocaml_int.to_int i))
  | Tagged_immediate i ->
    Tagged_immediate (z_of_int (Target_ocaml_int.to_int i))
  | Null -> Null
  | Naked_int8 i -> Naked_int8 (z_of_int (Numeric_types.Int8.to_int i))
  | Naked_int16 i -> Naked_int16 (z_of_int (Numeric_types.Int16.to_int i))
  | Naked_int32 i -> Naked_int32 (z_of_int64 (Int64.of_int32 i))
  | Naked_int64 i -> Naked_int64 (z_of_int64 i)
  | Naked_nativeint i ->
    Naked_nativeint (z_of_int64 (Targetint_32_64.to_int64 i))
  | Naked_float32 f -> convert_float32 f
  | Naked_float f -> convert_float f
  | Naked_vec128 _ | Naked_vec256 _ | Naked_vec512 _ | Naked_mask _ | Poison _
    ->
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
          let id = Code_ids.find code_id in
          Model.Bind_code (id, convert_code code) :: bindings)
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
  | Unary (p, arg) -> (
    match convert_unary_primitive p with
    | Some p -> Prim (Unary p, [convert_simple arg])
    | None -> unsupported "primitive %a" P.print prim)
  | Binary (p, arg1, arg2) -> (
    match convert_binary_primitive p with
    | Some p -> Prim (Binary p, [convert_simple arg1; convert_simple arg2])
    | None -> unsupported "primitive %a" P.print prim)
  | Variadic (p, args) -> (
    match convert_variadic_primitive p ~num_args:(List.length args) with
    | Some p -> Prim (Variadic p, convert_simples args)
    | None -> unsupported "primitive %a" P.print prim)
  | Nullary _ | Ternary _ | Quaternary _ ->
    unsupported "primitive %a" P.print prim

and convert_or_variable : type a.
    (a -> Model.const) -> a Or_variable.t -> Model.simple =
 fun convert contents ->
  match contents with
  | Const c -> Const (convert c)
  | Var (var, _) -> Var (Variables.find var)

(* A static block of the model is a tag and fields that are values, so a block
   with a mixed shape, whose flat suffix holds naked numbers, is not in the
   model. *)
and convert_static_const (const : Static_const.t) : Model.static_const =
  match const with
  | Block (tag, Immutable, Value_only, fields) ->
    Static_const_block
      ( z_of_int (Tag.Scannable.to_int tag),
        List.map
          (fun field -> convert_simple (Simple.With_debuginfo.simple field))
          fields )
  | Immutable_string s ->
    Static_const_immutable_string
      (List.init (String.length s) (fun i -> z_of_int (Char.code s.[i])))
  | Boxed_float32 contents ->
    Static_const_boxed_number (convert_or_variable convert_float32 contents)
  | Boxed_float contents ->
    Static_const_boxed_number (convert_or_variable convert_float contents)
  | Boxed_int32 contents ->
    Static_const_boxed_number
      (convert_or_variable
         (fun i : Model.const -> Naked_int32 (z_of_int64 (Int64.of_int32 i)))
         contents)
  | Boxed_int64 contents ->
    Static_const_boxed_number
      (convert_or_variable
         (fun i : Model.const -> Naked_int64 (z_of_int64 i))
         contents)
  | Boxed_nativeint contents ->
    Static_const_boxed_number
      (convert_or_variable
         (fun i : Model.const ->
           Naked_nativeint (z_of_int64 (Targetint_32_64.to_int64 i)))
         contents)
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
  | Naked of string * int64
  | Null
  | Block of int * observation list
  | Boxed of observation
  | String of string
  | Function
  | Dangling
  | Too_deep

let rec observe depth (statics : Values.static_env) (v : Values.value) :
    observation =
  if depth = 0
  then Too_deep
  else
    match v with
    | Value_const (Tagged_immediate i) -> Tagged (int_of_z i)
    | Value_const (Naked_immediate i) -> Naked ("imm", int64_of_z i)
    | Value_const (Naked_int8 i) -> Naked ("int8", int64_of_z i)
    | Value_const (Naked_int16 i) -> Naked ("int16", int64_of_z i)
    | Value_const (Naked_int32 i) -> Naked ("int32", int64_of_z i)
    | Value_const (Naked_int64 i) -> Naked ("int64", int64_of_z i)
    | Value_const (Naked_nativeint i) -> Naked ("nativeint", int64_of_z i)
    | Value_const (Naked_float32 bits) -> Naked ("float32", int64_of_z bits)
    | Value_const (Naked_float bits) -> Naked ("float", int64_of_z bits)
    | Value_const Null -> Null
    | Value_const _ -> Naked ("number", 0L)
    | Value_closure _ -> Function
    | Value_block (tag, fields) ->
      Block (int_of_z tag, List.map (observe (depth - 1) statics) fields)
    | Value_boxed_number c ->
      Boxed (observe (depth - 1) statics (Values.Value_const c))
    | Value_symbol symbol -> (
      match Maps.lookup symbol statics.static_values with
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
  | Naked (kind, i) -> Format.fprintf ppf "#%Ld:%s" i kind
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
        let values = List.map (observe 50 state.state_statics) values in
        ( (if k = unit.return_continuation
           then Returns values
           else if k = unit.exn_continuation
           then Raises values
           else Exits_elsewhere),
          steps )
  in
  go 0
    { state_expr = unit.body;
      state_vars = [];
      state_conts = [];
      state_statics = Values.empty_static_env
    }

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

let string_of_standard_int (kind : Kinds.standard_int) =
  match kind with
  | Standard_tagged_immediate -> "tagged_imm"
  | Standard_naked_immediate -> "imm"
  | Standard_naked_int8 -> "int8"
  | Standard_naked_int16 -> "int16"
  | Standard_naked_int32 -> "int32"
  | Standard_naked_int64 -> "int64"
  | Standard_naked_nativeint -> "nativeint"

let string_of_signedness (signedness : Primitives.signedness) =
  match signedness with Signed -> "" | Unsigned -> "unsigned_"

let print_prim ppf (p : Primitives.prim) =
  let unary (p : Primitives.unary_primitive) =
    match p with
    | Block_load (_, field) -> Printf.sprintf "Block_load %d" (int_of_z field)
    | Is_int variant_only -> if variant_only then "Is_int" else "Is_int_generic"
    | Is_null -> "Is_null"
    | Get_tag -> "Get_tag"
    | Opaque_identity _ -> "Opaque_identity"
    | Unbox_number _ -> "Unbox_number"
    | Box_number _ -> "Box_number"
    | Untag_immediate -> "Untag_immediate"
    | Tag_immediate -> "Tag_immediate"
  in
  let int_arith (op : Primitives.binary_int_arith_op) =
    match op with
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | Div signedness -> string_of_signedness signedness ^ "div"
    | Mod signedness -> string_of_signedness signedness ^ "mod"
    | And -> "and"
    | Or -> "or"
    | Xor -> "xor"
  in
  let int_comp (behaviour : Primitives.int_comparison_behaviour) =
    match behaviour with
    | Yielding_bool Int_eq -> "eq"
    | Yielding_bool Int_neq -> "neq"
    | Yielding_bool (Int_lt signedness) ->
      string_of_signedness signedness ^ "lt"
    | Yielding_bool (Int_gt signedness) ->
      string_of_signedness signedness ^ "gt"
    | Yielding_bool (Int_le signedness) ->
      string_of_signedness signedness ^ "le"
    | Yielding_bool (Int_ge signedness) ->
      string_of_signedness signedness ^ "ge"
    | Yielding_int_like_compare_functions signedness ->
      string_of_signedness signedness ^ "compare"
  in
  match p with
  | Unary p -> Format.pp_print_string ppf (unary p)
  | Binary (Int_arith (kind, op)) ->
    Format.fprintf ppf "Int_arith %s %s"
      (string_of_standard_int kind)
      (int_arith op)
  | Binary (Int_comp (kind, behaviour)) ->
    Format.fprintf ppf "Int_comp %s %s"
      (string_of_standard_int kind)
      (int_comp behaviour)
  | Variadic (Make_block (Block_kind_values tag)) ->
    Format.fprintf ppf "Make_block %d" (int_of_z tag)

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
    (* What the test above shows of one run, this shows of all. The whole check
       is [validate_unit], extracted from FlambdaValidateSpec.v, where it is
       proved that what it accepts is correct for the unit run on its own from
       empty environments. It normalises the two terms, compares them up to
       bound names and, failing that, removes from the term before the static
       bindings named here and compares again. Which names those are is a guess
       that it checks. *)
    let inlined = Normalise.inline_calls [] before.body in
    Format.printf
      "  calls outside code once those of known code are inlined: %d@."
      (calls_outside_code inlined);
    let rounds = nat_of_int 50 in
    let normalised_before = Validate.normalise_before rounds before.body in
    let unused = unused_statics normalised_before in
    let validation =
      Validate.validate_unit rounds unused before.body after.body
    in
    Format.printf "  %s@."
      (match validation with
      | Same_up_to_bound_names -> "validated: the same up to bound names"
      | Same_once_normalised -> "validated: the same once normalised"
      | Same_once_unused_statics_removed ->
        "validated: the same once normalised and unused static bindings removed"
      | Not_validated ->
        if outcome_before = Undefined
        then "nothing to validate, as the term before is undefined"
        else "not validated");
    (match validation with
    | Not_validated when Sys.getenv_opt "FLSEMANTICS_PRINT_TERMS" <> None ->
      Format.printf
        "@[<v 2>  the term before, normalised:@ %a@]@.@[<v 2>  the term after, \
         normalised:@ %a@]@."
        print_expr
        (Validate.without_statics unused normalised_before)
        print_expr
        (Validate.normalise_after rounds after.body)
    | Not_validated | Same_up_to_bound_names | Same_once_normalised
    | Same_once_unused_statics_removed ->
      ());
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
