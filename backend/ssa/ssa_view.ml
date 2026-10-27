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

open! Int_replace_polymorphic_compare

[@@@ocaml.warning "+a-40-41-42"]

(* See [ssa_view.mli] for the interface. *)

open Ssa.Export
module M = SsaModel

let value (v : finished Value.t) : M.value_view =
  match v with
  | Res ({ id; op; args; _ }, _) ->
    let op : M.op_view =
      match[@warning "-fragile-match"] op, args with
      | ( ( Const_int _ | Const_float _ | Const_float32 _ | Const_symbol _
          | Const_vec128 _ | Const_vec256 _ | Const_vec512 _ ),
          _ ) ->
        Op_const
      | Intop Iadd, [| x; y |] -> Op_add (x, y)
      | Intop Isub, [| x; y |] -> Op_sub (x, y)
      | Intop_imm (Iadd, c), [| x |] -> Op_add_imm (x, c)
      | Intop_imm (Isub, c), [| x |] -> Op_sub_imm (x, c)
      | Intop (Icomp cmp), [| x; y |] -> Op_comp (cmp, x, y)
      | Intop_imm (Icomp cmp, k), [| x |] -> Op_comp_imm (cmp, x, k)
      | _, _ -> Op_other
    in
    Res (id, op)
  | Block_param (block, index) -> Block_param (block, index)

let instr (i : finished Instruction.t) : M.instr_view =
  match i with
  | Op { id; args; _ } -> Op (id, Array.to_list args)
  | Push_trap _ -> Push_trap
  | Pop_trap _ -> Pop_trap

let terminator (b : finished Block.t) : M.Terminator.t =
  match Block.terminator b with
  | Continue { continuation; args } ->
    Continue (continuation, Array.to_list args)
  | Switch { index; targets } -> Switch (index, Array.to_list targets)
  | Call { args; _ } -> Call (Array.to_list args)
  | Invalid { args; _ } -> Invalid (Array.to_list args)

let params (b : finished Block.t) : finished Value.t list =
  Array.to_list (Block.params b)

let body (b : finished Block.t) : finished Instruction.t list =
  Array.to_list (Block.body b)

let strict_dominators (b : finished Block.t) : finished Block.t list =
  let rec walk (block : finished Block.t) acc =
    let idom = Block.immediate_dominator block in
    if Block.equal idom block then List.rev acc else walk idom (idom :: acc)
  in
  walk b []

let tree_of_value (v : finished Value.t) : M.tree =
  (* Bound the expanded tree, not the number of distinct SSA values: sharing
     the tree alone would still leave exponential traversals in the extracted
     recognizer and linearizer. An unexpanded value remains an exact atom.
     Reserve child nodes before descending so even the [Other] leaves fit the
     budget, and a long unary chain cannot exhaust the stack. *)
  let max_nodes = 256 in
  let remaining = ref (max_nodes - 1) in
  let rec walk (v : finished Value.t) =
    let unary a make =
      if !remaining < 1
      then M.Other v
      else begin
        decr remaining;
        make (walk a)
      end
    in
    let binary a b make =
      if !remaining < 2
      then M.Other v
      else begin
        remaining := !remaining - 2;
        let a = walk a in
        let b = walk b in
        make a b
      end
    in
    match[@warning "-fragile-match"] v with
    | Res ({ op = Const_int n; _ }, _) -> M.Const_int (v, Int64.of_nativeint n)
    | Res ({ op = Intop Iadd; args = [| a; b |]; _ }, _) ->
      binary a b (fun a b -> M.Iadd (v, a, b))
    | Res ({ op = Intop Isub; args = [| a; b |]; _ }, _) ->
      binary a b (fun a b -> M.Isub (v, a, b))
    | Res ({ op = Intop_imm (Iadd, k); args = [| a |]; _ }, _) ->
      unary a (fun a -> M.Iadd_imm (v, a, k))
    | Res ({ op = Intop_imm (Isub, k); args = [| a |]; _ }, _) ->
      unary a (fun a -> M.Isub_imm (v, a, k))
    | Res ({ op = Intop_imm (Ilsl, k); args = [| a |]; _ }, _) ->
      unary a (fun a -> M.Ilsl (v, a, k))
    | Res ({ op = Intop_imm (Iasr, k); args = [| a |]; _ }, _) ->
      unary a (fun a -> M.Iasr (v, a, k))
    | Res ({ op = Intop_imm (Ilsr, k); args = [| _ |]; _ }, _) -> M.Ilsr (v, k)
    | Res ({ op = Intop_imm (Ior, m); args = [| a |]; _ }, _) ->
      unary a (fun a -> M.Ior (v, a, m))
    | Res ({ op = Intop (Icomp cmp); args = [| a; b |]; _ }, _) ->
      binary a b (fun a b -> M.Icomp (v, cmp, a, b))
    | Res ({ op = Intop_imm (Icomp cmp, k); args = [| a |]; _ }, _) ->
      unary a (fun a -> M.Icomp_imm (v, cmp, a, k))
    | _ -> M.Other v
  in
  walk v

let compute_op_def (ssa : finished Ssa.graph) : M.op_def =
  let tbl : M.op_def = Instruction.Id.Tbl.create 64 in
  List.iter
    (fun (bl : finished Block.t) ->
      Array.iter
        (fun (i : finished Instruction.t) ->
          match i with
          | Op { id; _ } -> Instruction.Id.Tbl.replace tbl id bl
          | Push_trap _ | Pop_trap _ -> ())
        (Block.body bl))
    (Ssa.blocks ssa);
  tbl
