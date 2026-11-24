(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/unboxing/Unboxers.v, which follows
   middle_end/flambda2/simplify/unboxing/unboxers.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open! Simplify_import
open Port_monad

type number_decider =
  { param_name : string;
    kind : K.Naked_number_kind.t;
    prove_is_a_boxed_number : TE.t -> T.t -> unit T.proof_of_property coq_M
  }

(** val param_name : number_decider -> string **)

let param_name n = n.param_name

(** val kind : number_decider -> K.Naked_number_kind.t **)

let kind n = n.kind

(** val prove_is_a_boxed_number : number_decider -> TE.t -> T.t -> unit
    T.proof_of_property coq_M **)

let prove_is_a_boxed_number n = n.prove_is_a_boxed_number

module Coq__1 = struct
  type unboxer =
    { var_name : string;
      var_kind : Flambda_kind.t;
      poison_const : Const.t;
      unboxing_prim : Simple.t -> P.t coq_M;
      prove_simple :
        TE.t -> Name_mode.t -> T.t -> Simple.t T.meet_shortcut coq_M
    }
end

include Coq__1

(** val var_name : unboxer -> string **)

let var_name u = u.var_name

(** val var_kind : unboxer -> Flambda_kind.t **)

let var_kind u = u.var_kind

(** val poison_const : unboxer -> Const.t **)

let poison_const u = u.poison_const

(** val unboxing_prim : unboxer -> Simple.t -> P.t coq_M **)

let unboxing_prim u = u.unboxing_prim

(** val prove_simple : unboxer -> TE.t -> Name_mode.t -> T.t -> Simple.t
    T.meet_shortcut coq_M **)

let prove_simple u = u.prove_simple

module type Number_S = sig
  val decider : number_decider

  val unboxing_prim : Simple.t -> P.t coq_M

  val unboxer : unboxer
end

module Immediate = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "naked_immediate";
      kind = K.Naked_number_kind.Naked_immediate;
      prove_is_a_boxed_number = T.prove_is_a_tagged_immediate
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Untag_immediate, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "naked_immediate";
      var_kind = K.naked_immediate;
      poison_const =
        Const.const_poison K.naked_immediate "variant_unboxing_naked_immediate";
      unboxing_prim;
      prove_simple = T.meet_tagging_of_simple
    }
end

module Float32 = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_float32";
      kind = K.Naked_number_kind.Naked_float32;
      prove_is_a_boxed_number = T.prove_is_a_boxed_float32
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_float32, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_float32";
      var_kind = K.naked_float32;
      poison_const =
        Const.const_poison K.naked_float32 "variant_unboxing_float32";
      unboxing_prim;
      prove_simple = T.meet_boxed_float32_containing_simple
    }
end

module Float = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_float";
      kind = K.Naked_number_kind.Naked_float;
      prove_is_a_boxed_number = T.prove_is_a_boxed_float
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_float, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_float";
      var_kind = K.naked_float;
      poison_const = Const.const_poison K.naked_float "variant_unboxing_float";
      unboxing_prim;
      prove_simple = T.meet_boxed_float_containing_simple
    }
end

module Int32 = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_int32";
      kind = K.Naked_number_kind.Naked_int32;
      prove_is_a_boxed_number = T.prove_is_a_boxed_int32
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_int32, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_int32";
      var_kind = K.naked_int32;
      poison_const = Const.const_poison K.naked_int32 "variant_unboxing_int32";
      unboxing_prim;
      prove_simple = T.meet_boxed_int32_containing_simple
    }
end

module Int64 = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_int64";
      kind = K.Naked_number_kind.Naked_int64;
      prove_is_a_boxed_number = T.prove_is_a_boxed_int64
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_int64, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_int64";
      var_kind = K.naked_int64;
      poison_const = Const.const_poison K.naked_int64 "variant_unboxing_int64";
      unboxing_prim;
      prove_simple = T.meet_boxed_int64_containing_simple
    }
end

module Nativeint = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_nativeint";
      kind = K.Naked_number_kind.Naked_nativeint;
      prove_is_a_boxed_number = T.prove_is_a_boxed_nativeint
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_nativeint, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_nativeint";
      var_kind = K.naked_nativeint;
      poison_const =
        Const.const_poison K.naked_nativeint "variant_unboxing_nativeint";
      unboxing_prim;
      prove_simple = T.meet_boxed_nativeint_containing_simple
    }
end

module Vec128 = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_vec128";
      kind = K.Naked_number_kind.Naked_vec128;
      prove_is_a_boxed_number = T.prove_is_a_boxed_vec128
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_vec128, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_vec128";
      var_kind = K.naked_vec128;
      poison_const = Const.const_poison K.naked_vec128 "variant_unboxing_vec128";
      unboxing_prim;
      prove_simple = T.meet_boxed_vec128_containing_simple
    }
end

module Vec256 = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_vec256";
      kind = K.Naked_number_kind.Naked_vec256;
      prove_is_a_boxed_number = T.prove_is_a_boxed_vec256
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_vec256, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_vec256";
      var_kind = K.naked_vec256;
      poison_const = Const.const_poison K.naked_vec256 "variant_unxboing_vec256";
      unboxing_prim;
      prove_simple = T.meet_boxed_vec256_containing_simple
    }
end

module Vec512 = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_vec512";
      kind = K.Naked_number_kind.Naked_vec512;
      prove_is_a_boxed_number = T.prove_is_a_boxed_vec512
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_vec512, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_vec512";
      var_kind = K.naked_vec512;
      poison_const = Const.const_poison K.naked_vec512 "variant_unboxing_vec512";
      unboxing_prim;
      prove_simple = T.meet_boxed_vec512_containing_simple
    }
end

module Mask = struct
  (** val decider : number_decider **)

  let decider =
    { param_name = "unboxed_mask";
      kind = K.Naked_number_kind.Naked_mask;
      prove_is_a_boxed_number = T.prove_is_a_boxed_mask
    }

  (** val unboxing_prim : Simple.t -> P.t coq_M **)

  let unboxing_prim simple = P.Unary (Unbox_number Naked_mask, simple)

  (** val unboxer : unboxer **)

  let unboxer =
    { var_name = "unboxed_mask";
      var_kind = K.naked_mask;
      poison_const = Const.const_poison K.naked_mask "variant_unboxing_mask";
      unboxing_prim;
      prove_simple = T.meet_boxed_mask_containing_simple
    }
end

module Field = struct
  (** val unboxing_prim : P.Block_access_kind.t -> Simple.t ->
      Target_ocaml_int.t -> P.t coq_M **)

  let unboxing_prim bak block index =
    P.Unary
      ( (fun (x__1, x__2, x__3) ->
          (P.Block_load { kind = x__1; mut = x__2; field = x__3 }
            : P.unary_primitive))
          (bak, Immutable, index),
        block )

  (** val unboxer : Const.t -> P.Block_access_kind.t -> Target_ocaml_int.t ->
      unboxer coq_M **)

  let unboxer poison_const0 bak index =
    { var_name = "field_at_use";
      var_kind = P.Block_access_kind.element_kind_for_load bak;
      poison_const = poison_const0;
      Coq__1.unboxing_prim = (fun block -> unboxing_prim bak block index);
      prove_simple =
        (fun tenv min_name_mode t ->
          T.meet_block_field_simple tenv min_name_mode
            (P.Block_access_kind.element_kind_for_load bak)
            t index)
    }
end

module Closure_field = struct
  (** val unboxing_prim : Function_slot.t -> Simple.t -> Value_slot.t -> P.t
      coq_M **)

  let unboxing_prim function_slot closure value_slot =
    P.Unary
      ( (fun (x__1, x__2) ->
          (P.Project_value_slot { project_from = x__1; value_slot = x__2 }
            : P.unary_primitive))
          (function_slot, value_slot),
        closure )

  (** val unboxer : Function_slot.t -> Value_slot.t -> unboxer coq_M **)

  let unboxer function_slot value_slot =
    let poison_const0 =
      Const.const_poison
        (Value_slot.kind value_slot)
        "variant_unboxing_closure_field"
    in
    let var_kind0 = Value_slot.kind value_slot in
    { var_name = "closure_field_at_use";
      var_kind = var_kind0;
      poison_const = poison_const0;
      Coq__1.unboxing_prim =
        (fun closure -> unboxing_prim function_slot closure value_slot);
      prove_simple =
        (fun tenv min_name_mode t ->
          T.meet_project_value_slot_simple tenv min_name_mode t value_slot)
    }
end
