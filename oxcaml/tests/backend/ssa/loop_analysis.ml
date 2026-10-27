open Ssa.Export

let function_info : Ssa.Function_info.t =
  { sym_name = "loop_analysis";
    parameters = [];
    codegen_options = [];
    dbg = Debuginfo.none;
    poll = Lambda.Default_poll;
    ret_type = Cmm.typ_int
  }

let block graph params =
  Block.create graph ~params ~cold:false ~handler_dbg:Debuginfo.none

let emit graph cursor op args =
  (Cursor.emit_op graph cursor op Debuginfo.none Cmm.typ_int args).(0)

let finish graph cursor term =
  Cursor.finish_block graph cursor ~dbg:Debuginfo.none term

let goto target args : _ Terminator.t =
  Continue
    { continuation = Goto target;
      args = Array.map (fun v -> Terminator.Arg v) args
    }

type body_shape =
  | Straight
  | Diamond
  | Inner_cycle
  | Irreducible_cycle

(* The outer counter always advances towards ten and is dead. Only the control
   flow between header visits distinguishes these cases. The irreducible cycle
   has two entries, so rejecting nested natural loops alone would not
   suffice. *)
let loop shape =
  let graph = Ssa.create_graph function_info ~keep_unused_ops:false in
  let header = block graph Cmm.typ_int in
  let body = block graph [||] in
  let latch = block graph [||] in
  let exit = block graph [||] in
  let entry = Cursor.start (Ssa.entry graph) in
  let zero = emit graph entry (Const_int 0n) [||] in
  let flag = emit graph entry (Const_int 1n) [||] in
  finish graph entry (goto header [| zero |]);
  let cursor = Cursor.start header in
  let i = Block.param header 0 in
  let cond = emit graph cursor (Intop_imm (Icomp Cmm.Clt, 10)) [| i |] in
  finish graph cursor (Switch { index = cond; targets = [| exit; body |] });
  let cursor = Cursor.start body in
  let branches ~cycle =
    let left = block graph [||] in
    let right = block graph [||] in
    finish graph cursor (Switch { index = flag; targets = [| left; right |] });
    let cursor = Cursor.start left in
    if cycle
    then
      finish graph cursor
        (Switch { index = flag; targets = [| latch; right |] })
    else finish graph cursor (goto latch [||]);
    finish graph (Cursor.start right)
      (goto (if cycle then left else latch) [||])
  in
  (match shape with
  | Straight -> finish graph cursor (goto latch [||])
  | Inner_cycle ->
    finish graph cursor (Switch { index = flag; targets = [| latch; body |] })
  | Diamond -> branches ~cycle:false
  | Irreducible_cycle -> branches ~cycle:true);
  let cursor = Cursor.start latch in
  let next = emit graph cursor (Intop_imm (Iadd, 1)) [| i |] in
  finish graph cursor (goto header [| next |]);
  let cursor = Cursor.start exit in
  let result = emit graph cursor (Const_int 42n) [||] in
  finish graph cursor
    (Continue { continuation = Return; args = [| Arg result |] });
  Ssa.finish_graph graph

let check_loop shape expected =
  let graph = loop shape in
  let _, deleted =
    Delete_empty_loops.run ~ppf_dump:Format.err_formatter graph
  in
  assert (deleted = expected)

let graph_with_result build =
  let graph = Ssa.create_graph function_info ~keep_unused_ops:false in
  let cursor = Cursor.start (Ssa.entry graph) in
  let result = build (emit graph cursor) in
  finish graph cursor
    (Continue { continuation = Return; args = [| Arg result |] });
  let graph = Ssa.finish_graph graph in
  match Block.terminator (Ssa.entry graph) with
  | Continue { args = [| Arg result |]; _ } -> result
  | _ -> failwith "unexpected terminator"

let rec tree_size (tree : SsaModel.tree) =
  match tree with
  | Const_int _ | Ilsr _ | Other _ -> 1
  | Iadd (_, a, b) | Isub (_, a, b) | Icomp (_, _, a, b) ->
    1 + tree_size a + tree_size b
  | Iadd_imm (_, a, _)
  | Isub_imm (_, a, _)
  | Ilsl (_, a, _)
  | Iasr (_, a, _)
  | Ior (_, a, _)
  | Icomp_imm (_, _, a, _) ->
    1 + tree_size a

let check_atom result =
  let tree = Ssa_view.tree_of_value result in
  assert (Value.equal (SsaModel.root tree) result);
  (* This is a regression bound, deliberately larger than the implementation's
     budget. Both long paths and shared DAGs must produce a small tree. *)
  assert (tree_size tree <= 1024);
  let (form, _), ctx = AffineSsa.linearize AffineSsa.new_ctx [] tree in
  match form with
  | { FourierMotzkin.Affine.const = 0; terms = [(id, 1)] } ->
    assert (Value.equal (List.assoc id ctx.atoms) result)
  | _ -> failwith "expected an exact atom for the result"

let () =
  check_loop Straight 1;
  check_loop Diamond 1;
  check_loop Inner_cycle 0;
  check_loop Irreducible_cycle 0;
  (* Ordinary small expressions must still be expanded, not all atomized. *)
  let small =
    graph_with_result (fun emit ->
        let x = emit (Const_int 5n) [||] in
        emit (Intop_imm (Iadd, 7)) [| x |])
  in
  let (form, side), _ =
    AffineSsa.linearize AffineSsa.new_ctx [] (Ssa_view.tree_of_value small)
  in
  assert (form = { FourierMotzkin.Affine.const = 12; terms = [] });
  assert (side = []);
  let zero_shift =
    graph_with_result (fun emit ->
        let x = emit (Const_int (-1n)) [||] in
        emit (Intop_imm (Ilsr, 0)) [| x |])
  in
  check_atom zero_shift;
  (* The shared graph has only 34 instructions, but unbounded unfolding produces
     196607 nodes. The outer shift is deliberately not recognized by the
     linearizer: expansion must be bounded before it is called. *)
  let shared =
    graph_with_result (fun emit ->
        let x = ref (emit (Const_int 1n) [||]) in
        for _ = 1 to 16 do
          let shifted = emit (Intop_imm (Ilsl, 16)) [| !x |] in
          x := emit (Intop Isub) [| !x; shifted |]
        done;
        emit (Intop_imm (Ilsl, 16)) [| !x |])
  in
  check_atom shared;
  (* Also exercise both extracted traversals on a shared expression made
     entirely of recognized operations. *)
  let shared_add =
    graph_with_result (fun emit ->
        let x = ref (emit (Const_int 1n) [||]) in
        for _ = 1 to 16 do
          x := emit (Intop Iadd) [| !x; !x |]
        done;
        !x)
  in
  check_atom shared_add;
  let deep =
    graph_with_result (fun emit ->
        let x = ref (emit (Const_int 0n) [||]) in
        for _ = 1 to 2000 do
          x := emit (Intop_imm (Iadd, 1)) [| !x |]
        done;
        !x)
  in
  check_atom deep;
  print_endline "OK"
