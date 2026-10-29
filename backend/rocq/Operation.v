(* The operations of the backend's instructions: [Operation.t] and
   [Operation.integer_operation] (backend/operation.mli), as the SSA models see
   them. The two types are copies of the compiler's, constructor for
   constructor, and extraction maps them back onto the compiler's
   (OperationExtract.v), so that a model matches on the very operation that
   defines an SSA value. The payloads a model never looks inside are abstract
   types, each named after the compiler type standing for it.

   Nothing is proved here. What an operation computes is stated where it is
   relied on (backend/ssa/loop/rocq/AffineSsa.v, LoopTermination.v). *)

From OxCamlStdlib Require Import OxCamlInt OxCamlInt64.
From OxCamlBackend Require Import IntegerComparison.

(* The payloads the models do not look inside. *)
Parameter symbol vec128_bits vec256_bits vec512_bits : Type.
Parameter memory_chunk addressing_mode reinterpret_cast static_cast
  specific_operation : Type.
Parameter signedness load intop_atomic probe_is_enabled name_for_debugger
  alloc : Type.
Parameter int128_operation float_width float_operation test : Type.

(* [Operation.integer_operation], the constructors in the same order. *)
Inductive integer_operation : Type :=
  | Iadd
  | Isub
  | Imul
  | Imulh (s : signedness)
  | Idiv (s : signedness)
  | Imod (s : signedness)
  | Iand
  | Ior
  | Ixor
  | Ilsl
  | Ilsr
  | Iasr
  | Iclz
  | Ictz
  | Ipopcnt
  | Icomp (cmp : integer_comparison).

(* [Operation.t], the constructors in the same order and with the same names,
   except [Opaque_op] for [Opaque], a keyword in Rocq. *)
Inductive operation : Type :=
  | Move
  | Spill
  | Reload
  | Const_int (n : nativeint)
  | Const_float32 (n : int32)
  | Const_float (n : int64)
  | Const_symbol (s : symbol)
  | Const_vec128 (b : vec128_bits)
  | Const_vec256 (b : vec256_bits)
  | Const_vec512 (b : vec512_bits)
  | Const_mask (n : int64)
  | Stackoffset (n : int)
  | Load (l : load)
  | Store (chunk : memory_chunk) (addr : addressing_mode) (assign : bool)
  | Intop (op : integer_operation)
  | Int128op (op : int128_operation)
  | Intop_imm (op : integer_operation) (k : int)
  | Intop_atomic (a : intop_atomic)
  | Floatop (w : float_width) (op : float_operation)
  | Csel (t : test)
  | Reinterpret_cast (c : reinterpret_cast)
  | Static_cast (c : static_cast)
  | Probe_is_enabled (p : probe_is_enabled)
  | Opaque_op
  | Begin_region
  | End_region
  | Specific (s : specific_operation)
  | Name_for_debugger (n : name_for_debugger)
  | Dls_get
  | Tls_get
  | Domain_index
  | Poll
  | Pause
  | Alloc (a : alloc).
