(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows
   middle_end/flambda2/simplify/simplify_binary_primitive.ml at commit
   ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition under
   the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries
   [tmpN] and their order) is that of GUIDE.md; the functors of the file are
   Rocq functors, their module types are what the file uses of the
   compiler's module types, and three modules of the compiler are declared
   again (see the gaps below); the two sets that the compiler makes inside a
   functor by applying a functor of its library are lists, written here. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Array Bound_var Comparison_result Debuginfo
  Int_ids List Mutability Number_adjuncts Numeric_types Or_bottom
  Or_unknown_or_bottom Reg_width_const Scalar Simple Simplify_common
  Target_ocaml_int Target_system.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* PORT-GAP(verbatim): not from the compiler's file. Rocq cannot name a
   module [Set]: the declarations and the module types of this file say
   [Set_]. For the seven modules of [Number_adjuncts] that the functors of
   this file are applied to, this OCaml text gives the sets that name too,
   so that each module has the module type that Rocq prints. *)
(*OCAML
module Number_adjuncts = struct
  include Number_adjuncts

  module For_tagged_immediates = struct
    include For_tagged_immediates

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_naked_immediates = struct
    include For_naked_immediates

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int8s = struct
    include For_int8s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int16s = struct
    include For_int16s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int32s = struct
    include For_int32s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_int64s = struct
    include For_int64s

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end

  module For_nativeints = struct
    include For_nativeints

    module Num = struct
      include Num
      module Set_ = Set

      module Pair = struct
        include Pair
        module Set_ = Set
      end
    end
  end
end
OCAML*)

(* 18 *)
Module A := Number_adjuncts.

(* The integer -1 (GUIDE.md, section 2: a literal other than 0 and 1). *)
Definition im1 : int := (-1)%Z.
Extract Inlined Constant im1 => "(-1)".

(* PORT-GAP(init): 294 and 476, [let result_kind =
   K.Standard_int_or_float.to_kind arg_kind] is computed when the functor is
   applied. A functor of Rocq cannot hold a computation: the function is
   declared here as one without effects, which it is. *)
Parameter K_Standard_int_or_float_to_kind : K.Standard_int_or_float.t -> K.t.
Extract Inlined Constant K_Standard_int_or_float_to_kind =>
  "Flambda_kind.Standard_int_or_float.to_kind".

(* PORT-GAP(decl): three modules of the compiler that decl/ has in part
   only (it declares what the files call, and a functor needs the whole of
   what its module type names). They are declared again here, with [Set_]
   for [Set]; the OCaml definitions are not inlined, so that Rocq prints
   each as a module of the compiler's own values. *)
Module Target_ocaml_int_.
  Definition t : Type := Target_ocaml_int.t.
  Parameter compare : t -> t -> M int.
  Extract Constant compare => "Target_ocaml_int.compare".
  Module Set_.
    Definition elt : Type := Target_ocaml_int.t.
    Definition t : Type := Target_ocaml_int.Set_.t.
    Parameter is_empty : t -> M bool.
    Extract Constant is_empty => "Target_ocaml_int.Set.is_empty".
    Parameter cardinal : t -> M int.
    Extract Constant cardinal => "Target_ocaml_int.Set.cardinal".
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Constant fold => "Target_ocaml_int.Set.fold".
    Parameter of_list : list elt -> M t.
    Extract Constant of_list => "Target_ocaml_int.Set.of_list".
    Parameter get_singleton : t -> M (option elt).
    Extract Constant get_singleton => "Target_ocaml_int.Set.get_singleton".
  End Set_.
End Target_ocaml_int_.

Module Float_by_bit_pattern.
  Definition t : Type := Numeric_types.Float_by_bit_pattern.t.
  Parameter equal : t -> t -> M bool.
  Extract Constant equal => "Numeric_types.Float_by_bit_pattern.equal".
  Parameter compare : t -> t -> M int.
  Extract Constant compare => "Numeric_types.Float_by_bit_pattern.compare".
  Module Set_.
    Definition elt : Type := Numeric_types.Float_by_bit_pattern.t.
    Definition t : Type := Numeric_types.Float_by_bit_pattern.Set_.t.
    Parameter is_empty : t -> M bool.
    Extract Constant is_empty =>
      "Numeric_types.Float_by_bit_pattern.Set.is_empty".
    Parameter cardinal : t -> M int.
    Extract Constant cardinal =>
      "Numeric_types.Float_by_bit_pattern.Set.cardinal".
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Constant fold => "Numeric_types.Float_by_bit_pattern.Set.fold".
    Parameter of_list : list elt -> M t.
    Extract Constant of_list =>
      "Numeric_types.Float_by_bit_pattern.Set.of_list".
    Parameter get_singleton : t -> M (option elt).
    Extract Constant get_singleton =>
      "Numeric_types.Float_by_bit_pattern.Set.get_singleton".
  End Set_.
  Parameter one : t.
  Extract Constant one => "Numeric_types.Float_by_bit_pattern.one".
  Parameter minus_one : t.
  Extract Constant minus_one => "Numeric_types.Float_by_bit_pattern.minus_one".
  Parameter is_any_nan : t -> M bool.
  Extract Constant is_any_nan =>
    "Numeric_types.Float_by_bit_pattern.is_any_nan".
  Module IEEE_semantics.
    Parameter add : t -> t -> M t.
    Extract Constant add =>
      "Numeric_types.Float_by_bit_pattern.IEEE_semantics.add".
    Parameter sub : t -> t -> M t.
    Extract Constant sub =>
      "Numeric_types.Float_by_bit_pattern.IEEE_semantics.sub".
    Parameter mul : t -> t -> M t.
    Extract Constant mul =>
      "Numeric_types.Float_by_bit_pattern.IEEE_semantics.mul".
    Parameter div : t -> t -> M t.
    Extract Constant div =>
      "Numeric_types.Float_by_bit_pattern.IEEE_semantics.div".
    Parameter equal : t -> t -> M bool.
    Extract Constant equal =>
      "Numeric_types.Float_by_bit_pattern.IEEE_semantics.equal".
    Parameter compare : t -> t -> M int.
    Extract Constant compare =>
      "Numeric_types.Float_by_bit_pattern.IEEE_semantics.compare".
  End IEEE_semantics.
  Module Pair.
    Definition t : Type :=
      (Numeric_types.Float_by_bit_pattern.t
       * Numeric_types.Float_by_bit_pattern.t)%type.
    Module Set_.
      Definition elt : Type :=
        (Numeric_types.Float_by_bit_pattern.t
         * Numeric_types.Float_by_bit_pattern.t)%type.
      Parameter t : Type.
      Extract Constant t => "Numeric_types.Float_by_bit_pattern.Pair.Set.t".
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Constant fold =>
        "Numeric_types.Float_by_bit_pattern.Pair.Set.fold".
    End Set_.
  End Pair.
  Parameter cross_product : Set_.t -> Set_.t -> M Pair.Set_.t.
  Extract Constant cross_product =>
    "Numeric_types.Float_by_bit_pattern.cross_product".
End Float_by_bit_pattern.

Module Float32_by_bit_pattern.
  Definition t : Type := Numeric_types.Float32_by_bit_pattern.t.
  Parameter equal : t -> t -> M bool.
  Extract Constant equal => "Numeric_types.Float32_by_bit_pattern.equal".
  Parameter compare : t -> t -> M int.
  Extract Constant compare => "Numeric_types.Float32_by_bit_pattern.compare".
  Module Set_.
    Definition elt : Type := Numeric_types.Float32_by_bit_pattern.t.
    Definition t : Type := Numeric_types.Float32_by_bit_pattern.Set_.t.
    Parameter is_empty : t -> M bool.
    Extract Constant is_empty =>
      "Numeric_types.Float32_by_bit_pattern.Set.is_empty".
    Parameter cardinal : t -> M int.
    Extract Constant cardinal =>
      "Numeric_types.Float32_by_bit_pattern.Set.cardinal".
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Extract Constant fold => "Numeric_types.Float32_by_bit_pattern.Set.fold".
    Parameter of_list : list elt -> M t.
    Extract Constant of_list =>
      "Numeric_types.Float32_by_bit_pattern.Set.of_list".
    Parameter get_singleton : t -> M (option elt).
    Extract Constant get_singleton =>
      "Numeric_types.Float32_by_bit_pattern.Set.get_singleton".
  End Set_.
  Parameter one : t.
  Extract Constant one => "Numeric_types.Float32_by_bit_pattern.one".
  Parameter minus_one : t.
  Extract Constant minus_one =>
    "Numeric_types.Float32_by_bit_pattern.minus_one".
  Parameter is_any_nan : t -> M bool.
  Extract Constant is_any_nan =>
    "Numeric_types.Float32_by_bit_pattern.is_any_nan".
  Module IEEE_semantics.
    Parameter add : t -> t -> M t.
    Extract Constant add =>
      "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.add".
    Parameter sub : t -> t -> M t.
    Extract Constant sub =>
      "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.sub".
    Parameter mul : t -> t -> M t.
    Extract Constant mul =>
      "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.mul".
    Parameter div : t -> t -> M t.
    Extract Constant div =>
      "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.div".
    Parameter equal : t -> t -> M bool.
    Extract Constant equal =>
      "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.equal".
    Parameter compare : t -> t -> M int.
    Extract Constant compare =>
      "Numeric_types.Float32_by_bit_pattern.IEEE_semantics.compare".
  End IEEE_semantics.
  Module Pair.
    Definition t : Type :=
      (Numeric_types.Float32_by_bit_pattern.t
       * Numeric_types.Float32_by_bit_pattern.t)%type.
    Module Set_.
      Definition elt : Type :=
        (Numeric_types.Float32_by_bit_pattern.t
         * Numeric_types.Float32_by_bit_pattern.t)%type.
      Parameter t : Type.
      Extract Constant t => "Numeric_types.Float32_by_bit_pattern.Pair.Set.t".
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Extract Constant fold =>
        "Numeric_types.Float32_by_bit_pattern.Pair.Set.fold".
    End Set_.
  End Pair.
  Parameter cross_product : Set_.t -> Set_.t -> M Pair.Set_.t.
  Extract Constant cross_product =>
    "Numeric_types.Float32_by_bit_pattern.cross_product".
End Float32_by_bit_pattern.

(* 20-27 *)
Inductive binary_arith_outcome_for_one_side_only (a : Type) : Type :=
| Exactly : a -> binary_arith_outcome_for_one_side_only a
| The_other_side : binary_arith_outcome_for_one_side_only a
| Negation_of_the_other_side : binary_arith_outcome_for_one_side_only a
| Bitwise_not_of_the_other_side :
    K.Standard_int.t -> binary_arith_outcome_for_one_side_only a
| Float_negation_of_the_other_side :
    Flambda_primitive.float_bitwidth -> binary_arith_outcome_for_one_side_only a
| Cannot_simplify : binary_arith_outcome_for_one_side_only a
| Invalid : binary_arith_outcome_for_one_side_only a.
Arguments Exactly {a} _.
Arguments The_other_side {a}.
Arguments Negation_of_the_other_side {a}.
Arguments Bitwise_not_of_the_other_side {a} _.
Arguments Float_negation_of_the_other_side {a} _.
Arguments Cannot_simplify {a}.
Arguments Invalid {a}.

(* PORT-GAP(decl): the module types of the compiler that the functors of
   this file name ([Container_types.S], [A.Int_number_kind],
   [Numeric_types.Float_by_bit_pattern]) are not declared in decl/. These
   four module types have what the file uses of them, with [Set_] for
   [Set]. [Pair_S] is [Container_types.S] for a module of pairs: its type
   and the fold of its sets. *)
Module Type Container_types_S.
  Parameter t : Type.
  Parameter compare : t -> t -> M int.
  Module Set_.
    Definition elt : Type := t.
    Parameter t : Type.
    Parameter is_empty : t -> M bool.
    Parameter cardinal : t -> M int.
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Parameter of_list : list elt -> M t.
    Parameter get_singleton : t -> M (option elt).
  End Set_.
End Container_types_S.

Module Type Pair_S.
  Parameter t : Type.
  Module Set_.
    Definition elt : Type := t.
    Parameter t : Type.
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
  End Set_.
End Pair_S.

Module Type Int_number_kind.
  Module Num.
    Parameter t : Type.
    Parameter equal : t -> t -> M bool.
    Parameter compare : t -> t -> M int.
    Module Set_.
      Definition elt : Type := t.
      Parameter t : Type.
      Parameter is_empty : t -> M bool.
      Parameter cardinal : t -> M int.
      Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
      Parameter of_list : list elt -> M t.
      Parameter get_singleton : t -> M (option elt).
    End Set_.
    Declare Module Pair : Pair_S with Definition t := (t * t)%type.
    Parameter cross_product : Set_.t -> Set_.t -> M Pair.Set_.t.
    Parameter zero : Target_system.Machine_width.t -> M t.
    Parameter one : Target_system.Machine_width.t -> M t.
    Parameter minus_one : Target_system.Machine_width.t -> M t.
    Parameter add : t -> t -> M t.
    Parameter sub : t -> t -> M t.
    Parameter mul : t -> t -> M t.
    Parameter div : t -> t -> M (option t).
    Parameter mod_ : t -> t -> M (option t).
    Parameter to_const : t -> M Reg_width_const.t.
    Parameter and_ : t -> t -> M t.
    Parameter or_ : t -> t -> M t.
    Parameter xor : t -> t -> M t.
    Parameter unsigned_div : t -> t -> M (option t).
    Parameter unsigned_mod : t -> t -> M (option t).
    Parameter shift_left : t -> Target_ocaml_int.t -> M t.
    Parameter shift_right : t -> Target_ocaml_int.t -> M t.
    Parameter shift_right_logical : t -> Target_ocaml_int.t -> M t.
    Parameter compare_unsigned : t -> t -> M int.
  End Num.
  Parameter standard_int_or_float_kind : K.Standard_int_or_float.t.
  Parameter unboxed_prover :
    T.Typing_env.t -> T.t -> M (T.meet_shortcut Num.Set_.t).
  Parameter these_unboxed : Num.Set_.t -> M T.t.
  Parameter term_unboxed : Num.t -> M Named.t.
  Parameter standard_int_kind : K.Standard_int.t.
End Int_number_kind.

Module Type Numeric_types_Float_by_bit_pattern.
  Parameter t : Type.
  Parameter equal : t -> t -> M bool.
  Parameter compare : t -> t -> M int.
  Module Set_.
    Definition elt : Type := t.
    Parameter t : Type.
    Parameter is_empty : t -> M bool.
    Parameter cardinal : t -> M int.
    Parameter fold : forall {A : Type}, (elt -> A -> M A) -> t -> A -> M A.
    Parameter of_list : list elt -> M t.
    Parameter get_singleton : t -> M (option elt).
  End Set_.
  Parameter one : t.
  Parameter minus_one : t.
  Parameter is_any_nan : t -> M bool.
  Module IEEE_semantics.
    Parameter add : t -> t -> M t.
    Parameter sub : t -> t -> M t.
    Parameter mul : t -> t -> M t.
    Parameter div : t -> t -> M t.
    Parameter equal : t -> t -> M bool.
    Parameter compare : t -> t -> M int.
  End IEEE_semantics.
  Declare Module Pair : Pair_S with Definition t := (t * t)%type.
  Parameter cross_product : Set_.t -> Set_.t -> M Pair.Set_.t.
End Numeric_types_Float_by_bit_pattern.

(* 29-76. The type [op] has the name of a value of the module type: it gets
   one [_]. The arguments are by place. *)
Module Type Binary_arith_like_sig.
  Declare Module Lhs : Container_types_S.

  Declare Module Rhs : Container_types_S.

  Declare Module Pair : Pair_S with Definition t := (Lhs.t * Rhs.t)%type.

  Declare Module Result : Container_types_S.

  Parameter ok_to_evaluate : DE.t -> M bool.

  Parameter cross_product : Lhs.Set_.t -> Rhs.Set_.t -> M Pair.Set_.t.

  Parameter arg_kind : K.Standard_int_or_float.t.

  Parameter result_kind : K.t.

  Parameter term : Result.t -> M Named.t.

  Parameter prover_lhs :
    T.Typing_env.t -> T.t -> M (T.meet_shortcut Lhs.Set_.t).

  Parameter prover_rhs :
    T.Typing_env.t -> T.t -> M (T.meet_shortcut Rhs.Set_.t).

  Parameter op_ : Type.

  Parameter unknown : Target_system.Machine_width.t -> op_ -> M T.t.

  Parameter these : Result.Set_.t -> M (T.t * option Simple.t).

  Parameter op :
    Target_system.Machine_width.t -> op_ -> Lhs.t -> Rhs.t ->
    M (option Result.t).

  Parameter op_lhs_unknown :
    Target_system.Machine_width.t -> op_ -> Rhs.t ->
    M (binary_arith_outcome_for_one_side_only Result.t).

  Parameter op_rhs_unknown :
    Target_system.Machine_width.t -> op_ -> Lhs.t ->
    M (binary_arith_outcome_for_one_side_only Result.t).
End Binary_arith_like_sig.

(* 78-277 *)
(* PORT-GAP(loose): 78-90, the signature of the functor (it shows [simplify]
   only) is not kept; 277, the attribute [@@inline always] is not kept. *)
Module Binary_arith_like (N : Binary_arith_like_sig).
  (* 91-130 *)
  Module Possible_result.
    (* 92-95 *)
    Inductive t : Type :=
    | Simple : Simple.t -> t
    | Prim : P.t -> t
    | Exactly : N.Result.t -> t.

    (* This signature aims to constrain the size of the [Set] module block,
       since this is duplicated a lot via inlining in the rest of this file. *)
    (* PORT-GAP(loose): 97-128, the compiler's [Set] is
       [Container_types.Make_set] applied to this type with [compare] and
       [print] (116-126), under a signature of six values (99-113). That
       functor of the compiler's library cannot be applied here (decl/ has
       no functors, and Rocq does not take a directive inside a functor):
       [compare] and [print] are ported, and the set with its six values is
       a list in the increasing order of [compare], without two equal
       elements. *)
    (* 116-124 *)
    Definition compare (t1 t2 : t) : M int :=
      match t1, t2 with
      | Simple simple1, Simple simple2 => Simple.compare simple1 simple2
      | Prim prim1, Prim prim2 => P.compare prim1 prim2
      | Exactly i1, Exactly i2 => N.Result.compare i1 i2
      | Simple _, (Prim _ | Exactly _) => ret im1
      | Prim _, Simple _ => ret 1
      | Prim _, Exactly _ => ret im1
      | Exactly _, (Simple _ | Prim _) => ret 1
      end.

    (* 126 *)
    Definition print (_ : Format.formatter) (_ : t) : M unit :=
      fatal_error "Not implemented".

    Module Set_.
      (* 100 *)
      Definition elt : Type := t.

      (* 102 *)
      Definition t : Type := list elt.

      (* 104 *)
      Definition empty : t := [].

      (* 106 *)
      Fixpoint add (elt : elt) (s : t) {struct s} : M t :=
        match s with
        | [] => ret [elt]
        | elt' :: rest =>
          let* c := compare elt elt' in
          if c <? 0
          then ret (elt :: s)
          else
            if c =? 0
            then ret s
            else
              let* rest := add elt rest in
              ret (elt' :: rest)
        end.

      (* 108 *)
      Definition is_empty (s : t) : M bool :=
        match s with [] => ret true | _ :: _ => ret false end.

      (* 110 *)
      Definition cardinal (s : t) : M int := List.length s.

      (* 112 *)
      Definition get_singleton (s : t) : M (option elt) :=
        match s with
        | [elt] => ret (Some elt)
        | [] | _ :: _ :: _ => ret None
        end.

      (* 114 *)
      Definition elements (s : t) : M (list elt) := ret s.
    End Set_.
  End Possible_result.

  (* 133 *)
  Definition max_num_possible_results : int := i10.

  (* 135-275. In the compiler: [op dacc ~original_term dbg ~arg1 ~arg1_ty
     ~arg2 ~arg2_ty ~result_var]. 137, [let module PR = Possible_result in]:
     the module is named in full. *)
  Definition simplify (op : N.op_) (dacc : DA.t) (original_term : Named.t)
      (dbg : Debuginfo.t) (arg1 : Simple.t) (arg1_ty : T.t) (arg2 : Simple.t)
      (arg2_ty : T.t) (result_var : Bound_var.t) : M SPR.t :=
    let* denv := DA.denv dacc in
    let* typing_env := DE.typing_env denv in
    let* proof1 := N.prover_lhs typing_env arg1_ty in
    let* proof2 := N.prover_rhs typing_env arg2_ty in
    let& kind := N.result_kind in
    (* PORT-GAP(loose): 143, the attribute [@inline always] is not kept. *)
    let& result_unknown :=
      fun (_ : unit) =>
      let* machine_width := DE.machine_width denv in
      let* dacc :=
        let! tmp1 := N.unknown machine_width op in
        DA.add_variable dacc result_var tmp1
      in
      SPR.create original_term false dacc
    in
    (* PORT-GAP(loose): 150, the attribute [@inline always] is not kept. *)
    let& result_invalid :=
      fun (_ : unit) =>
      let* dacc :=
        let! tmp1 := T.bottom kind in
        DA.add_variable dacc result_var tmp1
      in
      SPR.create_invalid dacc
    in
    (* 154-189 *)
    let& check_possible_results :=
      fun (possible_results : Possible_result.Set_.t) =>
      let! tmp1 := Possible_result.Set_.is_empty possible_results in
      if tmp1
      then result_invalid tt
      else
        let* named :=
          let! tmp2 := Possible_result.Set_.get_singleton possible_results in
          match tmp2 with
          | Some (Possible_result.Exactly i) => N.term i
          | Some (Possible_result.Prim prim) => Named.create_prim prim dbg
          | Some (Possible_result.Simple simple) => Named.create_simple simple
          | None => ret original_term
          end
        in
        let* '(ty, simple_opt) :=
          (* 171, [is]: a word of Rocq, it gets one [_]. *)
          let* is_ :=
            let! tmp3 := Possible_result.Set_.elements possible_results in
            List.filter_map
              (fun (possible_result : Possible_result.t) =>
                match possible_result with
                | Possible_result.Exactly i => ret (Some i)
                | Possible_result.Prim _ | Possible_result.Simple _ => ret None
                end)
              tmp3
          in
          let! tmp4 := Possible_result.Set_.cardinal possible_results in
          let! tmp5 := List.length is_ in
          if tmp5 =? tmp4
          then
            let! tmp6 := N.Result.Set_.of_list is_ in
            N.these tmp6
          else
            let! tmp7 := Possible_result.Set_.get_singleton possible_results in
            match tmp7 with
            | Some (Possible_result.Simple simple) =>
              let! tmp8 := T.alias_type_of kind simple in
              ret (tmp8, Some simple)
            | Some (Possible_result.Exactly _) | Some (Possible_result.Prim _)
            | None =>
              let* machine_width := DE.machine_width denv in
              let! tmp9 := N.unknown machine_width op in
              ret (tmp9, None)
            end
        in
        let* dacc := DA.add_variable dacc result_var ty in
        match simple_opt with
        | None => SPR.create named false dacc
        | Some simple =>
          let* named := Named.create_simple simple in
          SPR.create named false dacc
        end
    in
    (* 190-243. In the compiler: [op nums ~folder ~other_side]. *)
    (* PORT-GAP(loose): 190-243, the function is used for the two sides
       (263 and 269), at two types of numbers and of sets, and a local
       function that stays in the extracted text ([let&]) has one type. It
       is Rocq's own [let], with the two types as its first arguments: one
       function here, but in the extracted text Rocq writes its body at
       each of the two uses, with the arguments (all of them values) in the
       place of the parameters. [folder] is the fold of the sets of one
       side, at the type of the possible results. *)
    let only_one_side_known :=
      fun (num nums_t : Type)
          (op : num -> M (binary_arith_outcome_for_one_side_only N.Result.t))
          (nums : nums_t)
          (folder :
            (num -> option Possible_result.Set_.t ->
             M (option Possible_result.Set_.t)) ->
            nums_t -> option Possible_result.Set_.t ->
            M (option Possible_result.Set_.t))
          (other_side : Simple.t) =>
      let* possible_results :=
        folder
          (fun i possible_results =>
            match possible_results with
            | None => ret None
            | Some possible_results =>
              let! tmp1 := op i in
              match tmp1 with
              | Exactly result =>
                let! tmp2 :=
                  Possible_result.Set_.add (Possible_result.Exactly result)
                    possible_results
                in
                ret (Some tmp2)
              | The_other_side =>
                let! tmp2 :=
                  Possible_result.Set_.add (Possible_result.Simple other_side)
                    possible_results
                in
                ret (Some tmp2)
              | Negation_of_the_other_side =>
                let* standard_int_kind :=
                  match N.arg_kind with
                  | K.Standard_int_or_float.Tagged_immediate =>
                    ret K.Standard_int.Tagged_immediate
                  | K.Standard_int_or_float.Naked_immediate =>
                    ret K.Standard_int.Naked_immediate
                  | K.Standard_int_or_float.Naked_int8 =>
                    ret K.Standard_int.Naked_int8
                  | K.Standard_int_or_float.Naked_int16 =>
                    ret K.Standard_int.Naked_int16
                  | K.Standard_int_or_float.Naked_int32 =>
                    ret K.Standard_int.Naked_int32
                  | K.Standard_int_or_float.Naked_int64 =>
                    ret K.Standard_int.Naked_int64
                  | K.Standard_int_or_float.Naked_nativeint =>
                    ret K.Standard_int.Naked_nativeint
                  | K.Standard_int_or_float.Naked_float
                  | K.Standard_int_or_float.Naked_float32 =>
                    fatal_error
                      "Cannot use [Negation_of_the_other_side] with floats; use the float version instead"
                  end
                in
                let* machine_width := DE.machine_width denv in
                let* zero :=
                  let! tmp2 := K.Standard_int.to_kind standard_int_kind in
                  Simple.const_int_of_kind machine_width tmp2 0
                in
                let& prim :=
                  P.Binary (P.Int_arith_ standard_int_kind P.Sub) zero
                    other_side
                in
                let! tmp3 :=
                  Possible_result.Set_.add (Possible_result.Prim prim)
                    possible_results
                in
                ret (Some tmp3)
              | Bitwise_not_of_the_other_side kind =>
                let& prim := P.Unary (P.Int_arith kind P.Not) other_side in
                let! tmp2 :=
                  Possible_result.Set_.add (Possible_result.Prim prim)
                    possible_results
                in
                ret (Some tmp2)
              | Float_negation_of_the_other_side width =>
                let& prim := P.Unary (P.Float_arith width P.Neg) other_side in
                let! tmp2 :=
                  Possible_result.Set_.add (Possible_result.Prim prim)
                    possible_results
                in
                ret (Some tmp2)
              | Cannot_simplify => ret None
              | Invalid => ret (Some possible_results)
              end
            end)
          nums (Some Possible_result.Set_.empty)
      in
      match possible_results with
      | Some results => check_possible_results results
      | None => result_unknown tt
      end
    in
    (* 244-275: each of the first three cases has [when N.ok_to_evaluate
       denv]; where the answer is no, the case that follows them (272-273)
       is taken. *)
    match proof1, proof2 with
    | T.Known_result nums1, T.Known_result nums2 =>
      let! tmp1 := N.ok_to_evaluate denv in
      if tmp1
      then
        (let! tmp2 := N.Lhs.Set_.is_empty nums1 in
         assert_ (negb tmp2)) ;;
        (let! tmp3 := N.Rhs.Set_.is_empty nums2 in
         assert_ (negb tmp3)) ;;
        let! tmp4 := N.Lhs.Set_.cardinal nums1 in
        let! tmp5 :=
          or_else (tmp4 >? max_num_possible_results)
            (let! tmp6 := N.Rhs.Set_.cardinal nums2 in
             ret (tmp6 >? max_num_possible_results))
        in
        if tmp5
        then result_unknown tt
        else
          let* all_pairs := N.cross_product nums1 nums2 in
          let* possible_results :=
            N.Pair.Set_.fold
              (fun '(i1, i2) possible_results =>
                let* machine_width := DE.machine_width denv in
                let! tmp7 := N.op machine_width op i1 i2 in
                match tmp7 with
                | None => ret possible_results
                | Some result =>
                  Possible_result.Set_.add (Possible_result.Exactly result)
                    possible_results
                end)
              all_pairs Possible_result.Set_.empty
          in
          check_possible_results possible_results
      else result_unknown tt
    | T.Known_result nums1, T.Need_meet =>
      let! tmp1 := N.ok_to_evaluate denv in
      if tmp1
      then
        (let! tmp2 := N.Lhs.Set_.is_empty nums1 in
         assert_ (negb tmp2)) ;;
        let* machine_width := DE.machine_width denv in
        only_one_side_known N.Lhs.t N.Lhs.Set_.t
          (fun i => N.op_rhs_unknown machine_width op i)
          nums1
          (@N.Lhs.Set_.fold (option Possible_result.Set_.t))
          arg2
      else result_unknown tt
    | T.Need_meet, T.Known_result nums2 =>
      let! tmp1 := N.ok_to_evaluate denv in
      if tmp1
      then
        (let! tmp2 := N.Rhs.Set_.is_empty nums2 in
         assert_ (negb tmp2)) ;;
        let* machine_width := DE.machine_width denv in
        only_one_side_known N.Rhs.t N.Rhs.Set_.t
          (fun i => N.op_lhs_unknown machine_width op i)
          nums2
          (@N.Rhs.Set_.fold (option Possible_result.Set_.t))
          arg1
      else result_unknown tt
    | T.Need_meet, T.Need_meet => result_unknown tt
    | T.Invalid, _ | _, T.Invalid => result_invalid tt
    end.
End Binary_arith_like.

(* 279-439 *)
(* PORT-GAP(loose): 279-281, the signature of the functor
   ([Binary_arith_like_sig with type op = P.binary_int_arith_op]) is checked
   by Rocq ([<:]) and not printed; 439, the attribute [@@inline always] is
   not kept. *)
Module Int_ops_for_binary_arith (I : Int_number_kind) <: Binary_arith_like_sig.
  (* 282-284 *)
  Module Lhs := I.Num.
  Module Rhs := I.Num.
  Module Result := I.Num.

  (* 286 *)
  Definition op_ : Type := P.binary_int_arith_op.

  (* 288-290: There are never any restrictions on the constant propagation
     of integers, unlike for floats. *)
  Definition ok_to_evaluate (_env : DE.t) : M bool := ret true.

  (* 292 *)
  Definition arg_kind : K.Standard_int_or_float.t :=
    I.standard_int_or_float_kind.

  (* 294 *)
  Definition result_kind : K.t := K_Standard_int_or_float_to_kind arg_kind.

  (* 296 *)
  Definition prover_lhs := I.unboxed_prover.

  (* 298 *)
  Definition prover_rhs := I.unboxed_prover.

  (* 300-310 *)
  Definition unknown (_ : Target_system.Machine_width.t) (_ : op_) : M T.t :=
    match arg_kind with
    | K.Standard_int_or_float.Tagged_immediate => ret T.any_tagged_immediate
    | K.Standard_int_or_float.Naked_immediate => ret T.any_naked_immediate
    | K.Standard_int_or_float.Naked_float32 => ret T.any_naked_float32
    | K.Standard_int_or_float.Naked_float => ret T.any_naked_float
    | K.Standard_int_or_float.Naked_int8 => ret T.any_naked_int8
    | K.Standard_int_or_float.Naked_int16 => ret T.any_naked_int16
    | K.Standard_int_or_float.Naked_int32 => ret T.any_naked_int32
    | K.Standard_int_or_float.Naked_int64 => ret T.any_naked_int64
    | K.Standard_int_or_float.Naked_nativeint => ret T.any_naked_nativeint
    end.

  (* 312-319 *)
  Definition these (s : I.Num.Set_.t) : M (T.t * option Simple.t) :=
    let* ty := I.these_unboxed s in
    let* simple_opt :=
      let! tmp1 := I.Num.Set_.get_singleton s in
      match tmp1 with
      | None => ret None
      | Some i =>
        let! tmp2 := I.Num.to_const i in
        let! tmp3 := Simple.const tmp2 in
        ret (Some tmp3)
      end
    in
    ret (ty, simple_opt).

  (* 321 *)
  Definition term := I.term_unboxed.

  (* 323 *)
  Module Pair := I.Num.Pair.

  (* 325 *)
  Definition cross_product := I.Num.cross_product.

  (* 327-339 *)
  Definition op (_ : Target_system.Machine_width.t)
      (op : P.binary_int_arith_op) (n1 n2 : I.Num.t) : M (option I.Num.t) :=
    let& always_some :=
      fun (f : I.Num.t -> I.Num.t -> M I.Num.t) =>
      let! tmp1 := f n1 n2 in
      ret (Some tmp1)
    in
    match op with
    | P.Add => always_some I.Num.add
    | P.Sub => always_some I.Num.sub
    | P.Mul => always_some I.Num.mul
    | P.Div Scalar.Signedness.Signed => I.Num.div n1 n2
    | P.Mod Scalar.Signedness.Signed => I.Num.mod_ n1 n2
    | P.Div Scalar.Signedness.Unsigned => I.Num.unsigned_div n1 n2
    | P.Mod Scalar.Signedness.Unsigned => I.Num.unsigned_mod n1 n2
    | P.And => always_some I.Num.and_
    | P.Or => always_some I.Num.or_
    | P.Xor => always_some I.Num.xor
    end.

  (* 341-346 *)
  Inductive symmetric_op : Type :=
  | Add
  | Mul
  | And
  | Or
  | Xor.

  (* 348 *)
  Module Num := I.Num.

  (* 350-382. In the compiler: [~machine_width op ~this_side]. *)
  Definition symmetric_op_one_side_unknown
      (machine_width : Target_system.Machine_width.t) (op : symmetric_op)
      (this_side : Num.t) : M (binary_arith_outcome_for_one_side_only Num.t) :=
    match op with
    | Add =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal this_side tmp1 in
      if tmp2 then ret The_other_side else ret Cannot_simplify
    | Mul =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal this_side tmp1 in
      if tmp2
      then
        let! tmp3 := Num.zero machine_width in
        ret (Exactly tmp3)
      else
        let! tmp4 := Num.one machine_width in
        let! tmp5 := Num.equal this_side tmp4 in
        if tmp5
        then ret The_other_side
        else
          let! tmp6 := Num.minus_one machine_width in
          let! tmp7 := Num.equal this_side tmp6 in
          if tmp7 then ret Negation_of_the_other_side else ret Cannot_simplify
    | And =>
      let! tmp1 := Num.minus_one machine_width in
      let! tmp2 := Num.equal this_side tmp1 in
      if tmp2
      then ret The_other_side
      else
        let! tmp3 := Num.zero machine_width in
        let! tmp4 := Num.equal this_side tmp3 in
        if tmp4
        then
          let! tmp5 := Num.zero machine_width in
          ret (Exactly tmp5)
        else ret Cannot_simplify
    | Or =>
      let! tmp1 := Num.minus_one machine_width in
      let! tmp2 := Num.equal this_side tmp1 in
      if tmp2
      then
        let! tmp3 := Num.minus_one machine_width in
        ret (Exactly tmp3)
      else
        let! tmp4 := Num.zero machine_width in
        let! tmp5 := Num.equal this_side tmp4 in
        if tmp5 then ret The_other_side else ret Cannot_simplify
    | Xor =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal this_side tmp1 in
      if tmp2
      then ret The_other_side
      else
        let! tmp3 := Num.minus_one machine_width in
        let! tmp4 := Num.equal this_side tmp3 in
        if tmp4
        then ret (Bitwise_not_of_the_other_side I.standard_int_kind)
        else ret Cannot_simplify
    end.

  (* 384-423. In the compiler: [~machine_width op ~rhs]. *)
  Definition op_lhs_unknown (machine_width : Target_system.Machine_width.t)
      (op : P.binary_int_arith_op) (rhs : Num.t)
      : M (binary_arith_outcome_for_one_side_only Num.t) :=
    match op with
    | P.Add => symmetric_op_one_side_unknown machine_width Add rhs
    | P.Mul => symmetric_op_one_side_unknown machine_width Mul rhs
    | P.And => symmetric_op_one_side_unknown machine_width And rhs
    | P.Or => symmetric_op_one_side_unknown machine_width Or rhs
    | P.Xor => symmetric_op_one_side_unknown machine_width Xor rhs
    | P.Sub =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal rhs tmp1 in
      if tmp2 then ret The_other_side else ret Cannot_simplify
    | P.Div signedness =>
      (* Division ("safe" division, strictly speaking, in Lambda terminology) is
         translated to a conditional on the denominator followed by an unsafe
         division (the "Div" seen here) on the way into Flambda 2. So if the
         denominator turns out to be zero here, via the typing or whatever, then
         we're in unreachable code. *)
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal rhs tmp1 in
      if tmp2
      then ret Invalid
      else
        let! tmp3 := Num.one machine_width in
        let! tmp4 := Num.equal rhs tmp3 in
        if tmp4
        then ret The_other_side
        else
          let! tmp5 := Num.minus_one machine_width in
          let! tmp6 := Num.equal rhs tmp5 in
          if tmp6
             && match signedness with
                | Scalar.Signedness.Signed => true
                | Scalar.Signedness.Unsigned => false
                end
          then ret Negation_of_the_other_side
          else ret Cannot_simplify
    | P.Mod signedness =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal rhs tmp1 in
      if tmp2
      then ret Invalid
      else
        let! tmp3 := Num.one machine_width in
        let! tmp4 := Num.equal rhs tmp3 in
        if tmp4
        then
          let! tmp5 := Num.zero machine_width in
          ret (Exactly tmp5)
        else
          let! tmp6 := Num.minus_one machine_width in
          let! tmp7 := Num.equal rhs tmp6 in
          if tmp7
             && match signedness with
                | Scalar.Signedness.Signed => true
                | Scalar.Signedness.Unsigned => false
                end
          then
            let! tmp8 := Num.zero machine_width in
            ret (Exactly tmp8)
          else ret Cannot_simplify
    end.

  (* 425-437. In the compiler: [~machine_width op ~lhs]. *)
  Definition op_rhs_unknown (machine_width : Target_system.Machine_width.t)
      (op : P.binary_int_arith_op) (lhs : Num.t)
      : M (binary_arith_outcome_for_one_side_only Num.t) :=
    match op with
    | P.Add => symmetric_op_one_side_unknown machine_width Add lhs
    | P.Mul => symmetric_op_one_side_unknown machine_width Mul lhs
    | P.And => symmetric_op_one_side_unknown machine_width And lhs
    | P.Or => symmetric_op_one_side_unknown machine_width Or lhs
    | P.Xor => symmetric_op_one_side_unknown machine_width Xor lhs
    | P.Sub =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal lhs tmp1 in
      if tmp2 then ret Negation_of_the_other_side else ret Cannot_simplify
    | P.Div (Scalar.Signedness.Signed | Scalar.Signedness.Unsigned)
    | P.Mod (Scalar.Signedness.Signed | Scalar.Signedness.Unsigned) =>
      ret Cannot_simplify
    end.
End Int_ops_for_binary_arith.

(* 441-463 *)
Module Int_ops_for_binary_arith_tagged_immediate :=
  Int_ops_for_binary_arith (A.For_tagged_immediates).
Module Int_ops_for_binary_arith_naked_immediate :=
  Int_ops_for_binary_arith (A.For_naked_immediates).
Module Int_ops_for_binary_arith_int8 := Int_ops_for_binary_arith (A.For_int8s).
Module Int_ops_for_binary_arith_int16 :=
  Int_ops_for_binary_arith (A.For_int16s).
Module Int_ops_for_binary_arith_int32 :=
  Int_ops_for_binary_arith (A.For_int32s).
Module Int_ops_for_binary_arith_int64 :=
  Int_ops_for_binary_arith (A.For_int64s).
Module Int_ops_for_binary_arith_nativeint :=
  Int_ops_for_binary_arith (A.For_nativeints).
Module Binary_int_arith_tagged_immediate :=
  Binary_arith_like (Int_ops_for_binary_arith_tagged_immediate).
Module Binary_int_arith_naked_immediate :=
  Binary_arith_like (Int_ops_for_binary_arith_naked_immediate).
Module Binary_int_arith_int8 :=
  Binary_arith_like (Int_ops_for_binary_arith_int8).
Module Binary_int_arith_int16 :=
  Binary_arith_like (Int_ops_for_binary_arith_int16).
Module Binary_int_arith_int32 :=
  Binary_arith_like (Int_ops_for_binary_arith_int32).
Module Binary_int_arith_int64 :=
  Binary_arith_like (Int_ops_for_binary_arith_int64).
Module Binary_int_arith_nativeint :=
  Binary_arith_like (Int_ops_for_binary_arith_nativeint).

(* 465-567 *)
(* PORT-GAP(loose): 465-467, the signature of the functor is checked by
   Rocq ([<:]) and not printed; 567, the attribute [@@inline always] is not
   kept. *)
Module Int_ops_for_binary_shift (I : Int_number_kind) <: Binary_arith_like_sig.
  (* 468-470 *)
  Module Lhs := I.Num.
  Module Rhs := Target_ocaml_int_.
  Module Result := I.Num.

  (* 472 *)
  Definition op_ : Type := P.int_shift_op.

  (* 474 *)
  Definition arg_kind : K.Standard_int_or_float.t :=
    I.standard_int_or_float_kind.

  (* 476 *)
  Definition result_kind : K.t := K_Standard_int_or_float_to_kind arg_kind.

  (* 478 *)
  Definition ok_to_evaluate (_env : DE.t) : M bool := ret true.

  (* 480 *)
  Definition prover_lhs := I.unboxed_prover.

  (* 482 *)
  Definition prover_rhs := T.meet_naked_immediates.

  (* 484-494 *)
  Definition unknown (_ : Target_system.Machine_width.t) (_ : op_) : M T.t :=
    match arg_kind with
    | K.Standard_int_or_float.Tagged_immediate => ret T.any_tagged_immediate
    | K.Standard_int_or_float.Naked_immediate => ret T.any_naked_immediate
    | K.Standard_int_or_float.Naked_float32 => ret T.any_naked_float32
    | K.Standard_int_or_float.Naked_float => ret T.any_naked_float
    | K.Standard_int_or_float.Naked_int8 => ret T.any_naked_int8
    | K.Standard_int_or_float.Naked_int16 => ret T.any_naked_int16
    | K.Standard_int_or_float.Naked_int32 => ret T.any_naked_int32
    | K.Standard_int_or_float.Naked_int64 => ret T.any_naked_int64
    | K.Standard_int_or_float.Naked_nativeint => ret T.any_naked_nativeint
    end.

  (* 496-503 *)
  Definition these (s : I.Num.Set_.t) : M (T.t * option Simple.t) :=
    let* ty := I.these_unboxed s in
    let* simple_opt :=
      let! tmp1 := I.Num.Set_.get_singleton s in
      match tmp1 with
      | None => ret None
      | Some i =>
        let! tmp2 := I.Num.to_const i in
        let! tmp3 := Simple.const tmp2 in
        ret (Some tmp3)
      end
    in
    ret (ty, simple_opt).

  (* 505 *)
  Definition term := I.term_unboxed.

  (* 508-512 *)
  (* PORT-GAP(loose): 508-512, the compiler's [Pair] is
     [Container_types.Make_pair (Lhs) (Rhs)]. That functor of the compiler's
     library cannot be applied here (as at 97-128): of [Pair] the file uses
     the type, and the empty set, [add] and [fold] of its sets. A set of
     pairs is the list of the pairs added, the last one first; the pairs
     that [cross_product] adds are all different, and [fold] takes them in
     the order in which they were added. (The compiler's [fold] takes them
     in increasing order; the two orders are one when the folds of the two
     sides, which add them, are in increasing order.) *)
  Module Pair.
    (* 509 *)
    Definition t : Type := (Lhs.t * Rhs.t)%type.

    Module Set_.
      Definition elt : Type := t.

      Definition t : Type := list elt.

      Definition empty : t := [].

      Definition add (elt : elt) (s : t) : M t := ret (elt :: s).

      Fixpoint fold {A : Type} (f : elt -> A -> M A) (s : t) (acc : A)
          {struct s} : M A :=
        match s with
        | [] => ret acc
        | elt :: rest =>
          let* acc := fold f rest acc in
          f elt acc
        end.
    End Set_.
  End Pair.

  (* 514-520 *)
  Definition cross_product (set1 : Lhs.Set_.t) (set2 : Rhs.Set_.t)
      : M Pair.Set_.t :=
    Lhs.Set_.fold
      (fun elt1 result =>
        Rhs.Set_.fold
          (fun elt2 result => Pair.Set_.add (elt1, elt2) result)
          set2 result)
      set1 Pair.Set_.empty.

  (* 522 *)
  Module Num := I.Num.

  (* 524-529 *)
  Definition op (_ : Target_system.Machine_width.t) (op : P.int_shift_op)
      (n1 : Num.t) (n2 : Target_ocaml_int.t) : M (option Num.t) :=
    let& always_some :=
      fun (f : Num.t -> Target_ocaml_int.t -> M Num.t) =>
      let! tmp1 := f n1 n2 in
      ret (Some tmp1)
    in
    match op with
    | P.Lsl => always_some Num.shift_left
    | P.Lsr => always_some Num.shift_right_logical
    | P.Asr => always_some Num.shift_right
    end.

  (* 531-545. In the compiler: [~machine_width op ~rhs]. 533, [let module O =
     Target_ocaml_int in]: the module is named in full. *)
  Definition op_lhs_unknown (machine_width : Target_system.Machine_width.t)
      (op : P.int_shift_op) (rhs : Target_ocaml_int.t)
      : M (binary_arith_outcome_for_one_side_only Num.t) :=
    let& rhs := rhs in
    match op with
    | P.Lsl | P.Lsr | P.Asr =>
      (* Shifting either way by [Targetint_32_64.size] or above, or by a
         negative amount, is undefined.

         However note that we cannot produce [Invalid] unless the code is type
         unsafe, which it is not here. (Otherwise a GADT match might be reduced
         to only one possible case which it would be wrong to take.) *)
      let! tmp1 := Target_ocaml_int.zero machine_width in
      let! tmp2 := Target_ocaml_int.equal rhs tmp1 in
      if tmp2 then ret The_other_side else ret Cannot_simplify
    end.

  (* 547-565. In the compiler: [~machine_width op ~lhs]. *)
  Definition op_rhs_unknown (machine_width : Target_system.Machine_width.t)
      (op : P.int_shift_op) (lhs : Num.t)
      : M (binary_arith_outcome_for_one_side_only Num.t) :=
    (* In these cases we are giving a semantics for some cases where the
       right-hand side may be less than zero or greater than or equal to
       [Targetint_32_64.size]. These cases have undefined semantics, as above;
       however, it seems fine to give them a semantics since there is benefit to
       doing so in this particular case. (This is not the case for the situation
       in [op_lhs_unknown], above, where there would be no such benefit.) *)
    match op with
    | P.Lsl | P.Lsr =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal lhs tmp1 in
      if tmp2
      then
        let! tmp3 := Num.zero machine_width in
        ret (Exactly tmp3)
      else ret Cannot_simplify
    | P.Asr =>
      let! tmp1 := Num.zero machine_width in
      let! tmp2 := Num.equal lhs tmp1 in
      if tmp2
      then
        let! tmp3 := Num.zero machine_width in
        ret (Exactly tmp3)
      else
        let! tmp4 := Num.minus_one machine_width in
        let! tmp5 := Num.equal lhs tmp4 in
        if tmp5
        then
          let! tmp6 := Num.minus_one machine_width in
          ret (Exactly tmp6)
        else ret Cannot_simplify
    end.
End Int_ops_for_binary_shift.

(* 569-591 *)
Module Int_ops_for_binary_shift_tagged_immediate :=
  Int_ops_for_binary_shift (A.For_tagged_immediates).
Module Int_ops_for_binary_shift_naked_immediate :=
  Int_ops_for_binary_shift (A.For_naked_immediates).
Module Int_ops_for_binary_shift_int8 := Int_ops_for_binary_shift (A.For_int8s).
Module Int_ops_for_binary_shift_int16 :=
  Int_ops_for_binary_shift (A.For_int16s).
Module Int_ops_for_binary_shift_int32 :=
  Int_ops_for_binary_shift (A.For_int32s).
Module Int_ops_for_binary_shift_int64 :=
  Int_ops_for_binary_shift (A.For_int64s).
Module Int_ops_for_binary_shift_nativeint :=
  Int_ops_for_binary_shift (A.For_nativeints).
Module Binary_int_shift_tagged_immediate :=
  Binary_arith_like (Int_ops_for_binary_shift_tagged_immediate).
Module Binary_int_shift_naked_immediate :=
  Binary_arith_like (Int_ops_for_binary_shift_naked_immediate).
Module Binary_int_shift_int8 :=
  Binary_arith_like (Int_ops_for_binary_shift_int8).
Module Binary_int_shift_int16 :=
  Binary_arith_like (Int_ops_for_binary_shift_int16).
Module Binary_int_shift_int32 :=
  Binary_arith_like (Int_ops_for_binary_shift_int32).
Module Binary_int_shift_int64 :=
  Binary_arith_like (Int_ops_for_binary_shift_int64).
Module Binary_int_shift_nativeint :=
  Binary_arith_like (Int_ops_for_binary_shift_nativeint).

(* 593-679 *)
(* PORT-GAP(loose): 593-597, the signature of the functor is checked by
   Rocq ([<:]) and not printed; 679, the attribute [@@inline always] is not
   kept. *)
Module Int_ops_for_binary_comp (I : Int_number_kind) <: Binary_arith_like_sig.
  (* 598-600 *)
  Module Lhs := I.Num.
  Module Rhs := I.Num.
  Module Result := Target_ocaml_int_.

  (* 602 *)
  Definition op_ : Type := P.comparison_behaviour P.signed_or_unsigned.

  (* 604 *)
  Definition arg_kind : K.Standard_int_or_float.t :=
    I.standard_int_or_float_kind.

  (* 606 *)
  Definition result_kind : K.t := K.naked_immediate.

  (* 608 *)
  Definition ok_to_evaluate (_env : DE.t) : M bool := ret true.

  (* 610 *)
  Definition prover_lhs := I.unboxed_prover.

  (* 612 *)
  Definition prover_rhs := I.unboxed_prover.

  (* 614-620 *)
  Definition unknown (machine_width : Target_system.Machine_width.t)
      (op : op_) : M T.t :=
    match op with
    | P.Yielding_bool _ =>
      let! tmp1 := Target_ocaml_int.all_bools machine_width in
      T.these_naked_immediates tmp1
    | P.Yielding_int_like_compare_functions _signedness =>
      let! tmp1 := Target_ocaml_int.zero_one_and_minus_one machine_width in
      T.these_naked_immediates tmp1
    end.

  (* 622-629 *)
  Definition these (s : Target_ocaml_int.Set_.t) : M (T.t * option Simple.t) :=
    let* ty := T.these_naked_immediates s in
    let* simple_opt :=
      let! tmp1 := Target_ocaml_int.Set_.get_singleton s in
      match tmp1 with
      | None => ret None
      | Some i =>
        let! tmp2 := Reg_width_const.naked_immediate i in
        let! tmp3 := Simple.const tmp2 in
        ret (Some tmp3)
      end
    in
    ret (ty, simple_opt).

  (* 631-632 *)
  Definition term (imm : Target_ocaml_int.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_immediate imm in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.

  (* 634 *)
  Module Pair := I.Num.Pair.

  (* 636 *)
  Definition cross_product := I.Num.cross_product.

  (* 638 *)
  Module Num := I.Num.

  (* 640-673 *)
  Definition op (machine_width : Target_system.Machine_width.t)
      (op : P.comparison_behaviour P.signed_or_unsigned) (n1 n2 : Num.t)
      : M (option Target_ocaml_int.t) :=
    match op with
    | P.Yielding_bool op =>
      let& bool :=
        fun (b : Datatypes.bool) => Target_ocaml_int.bool_ machine_width b
      in
      match op with
      | P.Eq =>
        let! tmp1 := Num.compare n1 n2 in
        let! tmp2 := bool (tmp1 =? 0) in
        ret (Some tmp2)
      | P.Neq =>
        let! tmp1 := Num.compare n1 n2 in
        let! tmp2 := bool (tmp1 <>? 0) in
        ret (Some tmp2)
      | P.Lt P.Signed =>
        let! tmp1 := Num.compare n1 n2 in
        let! tmp2 := bool (tmp1 <? 0) in
        ret (Some tmp2)
      | P.Gt P.Signed =>
        let! tmp1 := Num.compare n1 n2 in
        let! tmp2 := bool (tmp1 >? 0) in
        ret (Some tmp2)
      | P.Le P.Signed =>
        let! tmp1 := Num.compare n1 n2 in
        let! tmp2 := bool (tmp1 <=? 0) in
        ret (Some tmp2)
      | P.Ge P.Signed =>
        let! tmp1 := Num.compare n1 n2 in
        let! tmp2 := bool (tmp1 >=? 0) in
        ret (Some tmp2)
      | P.Lt P.Unsigned =>
        let! tmp1 := Num.compare_unsigned n1 n2 in
        let! tmp2 := bool (tmp1 <? 0) in
        ret (Some tmp2)
      | P.Gt P.Unsigned =>
        let! tmp1 := Num.compare_unsigned n1 n2 in
        let! tmp2 := bool (tmp1 >? 0) in
        ret (Some tmp2)
      | P.Le P.Unsigned =>
        let! tmp1 := Num.compare_unsigned n1 n2 in
        let! tmp2 := bool (tmp1 <=? 0) in
        ret (Some tmp2)
      | P.Ge P.Unsigned =>
        let! tmp1 := Num.compare_unsigned n1 n2 in
        let! tmp2 := bool (tmp1 >=? 0) in
        ret (Some tmp2)
      end
    | P.Yielding_int_like_compare_functions signed_or_unsigned =>
      match signed_or_unsigned with
      | P.Signed =>
        let& int :=
          fun (i : Port_monad.int) => Target_ocaml_int.of_int machine_width i
        in
        let* c := Num.compare n1 n2 in
        if c <? 0
        then
          let! tmp1 := int im1 in
          ret (Some tmp1)
        else
          if c =? 0
          then
            let! tmp2 := int 0 in
            ret (Some tmp2)
          else
            let! tmp3 := int 1 in
            ret (Some tmp3)
      | P.Unsigned =>
        let& int :=
          fun (i : Port_monad.int) => Target_ocaml_int.of_int machine_width i
        in
        let* c := Num.compare_unsigned n1 n2 in
        if c <? 0
        then
          let! tmp1 := int im1 in
          ret (Some tmp1)
        else
          if c =? 0
          then
            let! tmp2 := int 0 in
            ret (Some tmp2)
          else
            let! tmp3 := int 1 in
            ret (Some tmp3)
      end
    end.

  (* 675. In the compiler: [~machine_width:_ _op ~rhs:_]. *)
  Definition op_lhs_unknown (_ : Target_system.Machine_width.t) (_op : op_)
      (_ : Num.t)
      : M (binary_arith_outcome_for_one_side_only Target_ocaml_int.t) :=
    ret Cannot_simplify.

  (* 677. In the compiler: [~machine_width:_ _op ~lhs:_]. *)
  Definition op_rhs_unknown (_ : Target_system.Machine_width.t) (_op : op_)
      (_ : Num.t)
      : M (binary_arith_outcome_for_one_side_only Target_ocaml_int.t) :=
    ret Cannot_simplify.
End Int_ops_for_binary_comp.

(* 681-700 *)
Module Int_ops_for_binary_comp_tagged_immediate :=
  Int_ops_for_binary_comp (A.For_tagged_immediates).
Module Int_ops_for_binary_comp_naked_immediate :=
  Int_ops_for_binary_comp (A.For_naked_immediates).
Module Int_ops_for_binary_comp_int8 := Int_ops_for_binary_comp (A.For_int8s).
Module Int_ops_for_binary_comp_int16 := Int_ops_for_binary_comp (A.For_int16s).
Module Int_ops_for_binary_comp_int32 := Int_ops_for_binary_comp (A.For_int32s).
Module Int_ops_for_binary_comp_int64 := Int_ops_for_binary_comp (A.For_int64s).
Module Int_ops_for_binary_comp_nativeint :=
  Int_ops_for_binary_comp (A.For_nativeints).
Module Binary_int_comp_tagged_immediate :=
  Binary_arith_like (Int_ops_for_binary_comp_tagged_immediate).
Module Binary_int_comp_naked_immediate :=
  Binary_arith_like (Int_ops_for_binary_comp_naked_immediate).
Module Binary_int_comp_int8 := Binary_arith_like (Int_ops_for_binary_comp_int8).
Module Binary_int_comp_int16 :=
  Binary_arith_like (Int_ops_for_binary_comp_int16).
Module Binary_int_comp_int32 :=
  Binary_arith_like (Int_ops_for_binary_comp_int32).
Module Binary_int_comp_int64 :=
  Binary_arith_like (Int_ops_for_binary_comp_int64).
Module Binary_int_comp_nativeint :=
  Binary_arith_like (Int_ops_for_binary_comp_nativeint).

(* 702-813 *)
(* PORT-GAP(loose): 702-720, the module type of the functor's argument,
   which the compiler writes in place, has a name; the signature of the
   functor is checked by Rocq ([<:]) and not printed. *)
Module Type Float_ops_for_binary_arith_gen_FP.
  Declare Module F : Numeric_types_Float_by_bit_pattern.

  Parameter width : Flambda_primitive.float_bitwidth.

  Parameter arg_kind : K.Standard_int_or_float.t.

  Parameter result_kind : Flambda_kind.t.

  Parameter prover : T.Typing_env.t -> T.t -> M (T.meet_shortcut F.Set_.t).

  Parameter unknown : T.t.

  Parameter these : F.Set_.t -> M T.t.

  Parameter const : F.t -> M Const.t.
End Float_ops_for_binary_arith_gen_FP.

Module Float_ops_for_binary_arith_gen (FP : Float_ops_for_binary_arith_gen_FP)
  <: Binary_arith_like_sig.
  (* 721-724 *)
  Module F := FP.F.
  Module Lhs := F.
  Module Rhs := F.
  Module Result := F.

  (* 726 *)
  Definition op_ : Type := P.binary_float_arith_op.

  (* 728 *)
  Definition arg_kind : K.Standard_int_or_float.t := FP.arg_kind.

  (* 730 *)
  Definition result_kind : K.t := FP.result_kind.

  (* 732 *)
  Definition ok_to_evaluate (denv : DE.t) : M bool :=
    DE.propagating_float_consts denv.

  (* 734 *)
  Definition prover_lhs := FP.prover.

  (* 736 *)
  Definition prover_rhs := FP.prover.

  (* 738 *)
  Definition unknown (_ : Target_system.Machine_width.t) (_ : op_) : M T.t :=
    ret FP.unknown.

  (* 740-747 *)
  Definition these (s : F.Set_.t) : M (T.t * option Simple.t) :=
    let* ty := FP.these s in
    let* simple_opt :=
      let! tmp1 := F.Set_.get_singleton s in
      match tmp1 with
      | None => ret None
      | Some f =>
        let! tmp2 := FP.const f in
        let! tmp3 := Simple.const tmp2 in
        ret (Some tmp3)
      end
    in
    ret (ty, simple_opt).

  (* 749 *)
  Definition term (f : F.t) : M Named.t :=
    let! tmp1 := FP.const f in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.

  (* 751 *)
  Module Pair := F.Pair.

  (* 753 *)
  Definition cross_product := F.cross_product.

  (* 755-761 *)
  Definition op (_ : Target_system.Machine_width.t) (op : op_) (n1 n2 : F.t)
      : M (option F.t) :=
    let& always_some :=
      fun (f : F.t -> F.t -> M F.t) =>
      let! tmp1 := f n1 n2 in
      ret (Some tmp1)
    in
    match op with
    | P.Add_ => always_some F.IEEE_semantics.add
    | P.Sub_ => always_some F.IEEE_semantics.sub
    | P.Mul_ => always_some F.IEEE_semantics.mul
    | P.Div_ => always_some F.IEEE_semantics.div
    end.

  (* 763-765 *)
  Inductive symmetric_op : Type :=
  | Add
  | Mul.

  (* To be certain of correctness we restrict identities on floating-point
     numbers to those that preserve the _bit pattern_. *)

  (* 770-789. In the compiler: [op ~this_side]. *)
  (* PORT-GAP(loose): 778-779 and 783-784, the four attributes [@z3 ...] on
     the answers are not kept. *)
  Definition symmetric_op_one_side_unknown (op : symmetric_op)
      (this_side : F.t) : M (binary_arith_outcome_for_one_side_only F.t) :=
    match op with
    | Add =>
      (* You might think that "x + 0" has the same representation as "x".
         However it doesn't in the case where that constant zero is +0 and x is
         equal to -0. *)
      ret Cannot_simplify
    | Mul =>
      let! tmp1 := F.equal this_side F.one in
      if tmp1
      then ret The_other_side
      else
        let! tmp2 := F.equal this_side F.minus_one in
        if tmp2
        then ret (Float_negation_of_the_other_side FP.width)
        else ret Cannot_simplify
    end.

  (* 791-804. In the compiler: [~machine_width:_ op ~rhs]. *)
  (* PORT-GAP(loose): 799 and 803, the two attributes [@z3 ...] on the
     answers are not kept. *)
  Definition op_lhs_unknown (_ : Target_system.Machine_width.t) (op : op_)
      (rhs : F.t) : M (binary_arith_outcome_for_one_side_only F.t) :=
    match op with
    | P.Add_ => symmetric_op_one_side_unknown Add rhs
    | P.Mul_ => symmetric_op_one_side_unknown Mul rhs
    | P.Sub_ => ret Cannot_simplify
    | P.Div_ =>
      let! tmp1 := F.equal rhs F.one in
      if tmp1
      then ret The_other_side
      else
        let! tmp2 := F.equal rhs F.minus_one in
        if tmp2
        then ret (Float_negation_of_the_other_side FP.width)
        else ret Cannot_simplify
    end.

  (* 806-812. In the compiler: [~machine_width:_ op ~lhs]. *)
  Definition op_rhs_unknown (_ : Target_system.Machine_width.t) (op : op_)
      (lhs : F.t) : M (binary_arith_outcome_for_one_side_only F.t) :=
    match op with
    | P.Add_ => symmetric_op_one_side_unknown Add lhs
    | P.Mul_ => symmetric_op_one_side_unknown Mul lhs
    | P.Sub_ => ret Cannot_simplify
    | P.Div_ => ret Cannot_simplify
    end.
End Float_ops_for_binary_arith_gen.

(* 815-831 *)
(* PORT-GAP(loose): 815-849, the argument of each application, which the
   compiler writes in place, is a module with a name. *)
Module Float_ops_for_binary_arith_FP.
  Module F := Float_by_bit_pattern.

  Definition width : Flambda_primitive.float_bitwidth :=
    Flambda_primitive.Float64.

  Definition arg_kind : K.Standard_int_or_float.t :=
    K.Standard_int_or_float.Naked_float.

  Definition result_kind : Flambda_kind.t := K.naked_float.

  Definition prover := T.meet_naked_floats.

  Definition unknown : T.t := T.any_naked_float.

  Definition these := T.these_naked_floats.

  Definition const := Reg_width_const.naked_float.
End Float_ops_for_binary_arith_FP.

Module Float_ops_for_binary_arith :=
  Float_ops_for_binary_arith_gen (Float_ops_for_binary_arith_FP).

(* 833-849 *)
Module Float32_ops_for_binary_arith_FP.
  Module F := Float32_by_bit_pattern.

  Definition width : Flambda_primitive.float_bitwidth :=
    Flambda_primitive.Float32.

  Definition arg_kind : K.Standard_int_or_float.t :=
    K.Standard_int_or_float.Naked_float32.

  Definition result_kind : Flambda_kind.t := K.naked_float32.

  Definition prover := T.meet_naked_float32s.

  Definition unknown : T.t := T.any_naked_float32.

  Definition these := T.these_naked_float32s.

  Definition const := Reg_width_const.naked_float32.
End Float32_ops_for_binary_arith_FP.

Module Float32_ops_for_binary_arith :=
  Float_ops_for_binary_arith_gen (Float32_ops_for_binary_arith_FP).

(* 851-852 *)
Module Binary_float_arith := Binary_arith_like (Float_ops_for_binary_arith).
Module Binary_float32_arith := Binary_arith_like (Float32_ops_for_binary_arith).

(* 854-960 *)
(* PORT-GAP(loose): 854-862, the module type of the functor's argument,
   which the compiler writes in place, has a name; the signature of the
   functor is checked by Rocq ([<:]) and not printed. *)
Module Type Float_ops_for_binary_comp_gen_FP.
  Declare Module F : Numeric_types_Float_by_bit_pattern.

  Parameter arg_kind : K.Standard_int_or_float.t.

  Parameter prover : T.Typing_env.t -> T.t -> M (T.meet_shortcut F.Set_.t).
End Float_ops_for_binary_comp_gen_FP.

Module Float_ops_for_binary_comp_gen (FP : Float_ops_for_binary_comp_gen_FP)
  <: Binary_arith_like_sig.
  (* 863-866 *)
  Module F := FP.F.
  Module Lhs := F.
  Module Rhs := F.
  Module Result := Target_ocaml_int_.

  (* 868 *)
  Definition op_ : Type := P.comparison_behaviour unit.

  (* 870 *)
  Definition arg_kind : K.Standard_int_or_float.t := FP.arg_kind.

  (* 872 *)
  Definition result_kind : K.t := K.naked_immediate.

  (* 874 *)
  Definition ok_to_evaluate (denv : DE.t) : M bool :=
    DE.propagating_float_consts denv.

  (* 876 *)
  Definition prover_lhs := FP.prover.

  (* 878 *)
  Definition prover_rhs := FP.prover.

  (* 880-886 *)
  Definition unknown (machine_width : Target_system.Machine_width.t)
      (op : op_) : M T.t :=
    match op with
    | P.Yielding_bool _ =>
      let! tmp1 := Target_ocaml_int.all_bools machine_width in
      T.these_naked_immediates tmp1
    | P.Yielding_int_like_compare_functions tt =>
      let! tmp1 := Target_ocaml_int.zero_one_and_minus_one machine_width in
      T.these_naked_immediates tmp1
    end.

  (* 888-895 *)
  Definition these (s : Target_ocaml_int.Set_.t) : M (T.t * option Simple.t) :=
    let* ty := T.these_naked_immediates s in
    let* simple_opt :=
      let! tmp1 := Target_ocaml_int.Set_.get_singleton s in
      match tmp1 with
      | None => ret None
      | Some i =>
        let! tmp2 := Reg_width_const.naked_immediate i in
        let! tmp3 := Simple.const tmp2 in
        ret (Some tmp3)
      end
    in
    ret (ty, simple_opt).

  (* 897-898 *)
  Definition term (imm : Target_ocaml_int.t) : M Named.t :=
    let! tmp1 := Reg_width_const.naked_immediate imm in
    let! tmp2 := Simple.const tmp1 in
    Named.create_simple tmp2.

  (* 900 *)
  Module Pair := F.Pair.

  (* 902 *)
  Definition cross_product := F.cross_product.

  (* 904-935 *)
  Definition op (machine_width : Target_system.Machine_width.t) (op : op_)
      (n1 n2 : F.t) : M (option Target_ocaml_int.t) :=
    match op with
    | P.Yielding_bool op =>
      let* has_nan :=
        let! tmp1 := F.is_any_nan n1 in
        or_else tmp1 (F.is_any_nan n2)
      in
      let& bool :=
        fun (b : Datatypes.bool) => Target_ocaml_int.bool_ machine_width b
      in
      match op with
      | P.Eq =>
        let! tmp1 := F.IEEE_semantics.equal n1 n2 in
        let! tmp2 := bool tmp1 in
        ret (Some tmp2)
      | P.Neq =>
        let! tmp1 := F.IEEE_semantics.equal n1 n2 in
        let! tmp2 := bool (negb tmp1) in
        ret (Some tmp2)
      | P.Lt tt =>
        if has_nan
        then
          let! tmp1 := bool false in
          ret (Some tmp1)
        else
          let! tmp2 := F.IEEE_semantics.compare n1 n2 in
          let! tmp3 := bool (tmp2 <? 0) in
          ret (Some tmp3)
      | P.Gt tt =>
        if has_nan
        then
          let! tmp1 := bool false in
          ret (Some tmp1)
        else
          let! tmp2 := F.IEEE_semantics.compare n1 n2 in
          let! tmp3 := bool (tmp2 >? 0) in
          ret (Some tmp3)
      | P.Le tt =>
        if has_nan
        then
          let! tmp1 := bool false in
          ret (Some tmp1)
        else
          let! tmp2 := F.IEEE_semantics.compare n1 n2 in
          let! tmp3 := bool (tmp2 <=? 0) in
          ret (Some tmp3)
      | P.Ge tt =>
        if has_nan
        then
          let! tmp1 := bool false in
          ret (Some tmp1)
        else
          let! tmp2 := F.IEEE_semantics.compare n1 n2 in
          let! tmp3 := bool (tmp2 >=? 0) in
          ret (Some tmp3)
      end
    | P.Yielding_int_like_compare_functions tt =>
      let& int :=
        fun (i : Port_monad.int) => Target_ocaml_int.of_int machine_width i
      in
      let* c := F.IEEE_semantics.compare n1 n2 in
      if c <? 0
      then
        let! tmp1 := int im1 in
        ret (Some tmp1)
      else
        if c =? 0
        then
          let! tmp2 := int 0 in
          ret (Some tmp2)
        else
          let! tmp3 := int 1 in
          ret (Some tmp3)
    end.

  (* 937-941. In the compiler: [~machine_width op]. *)
  Definition result_of_comparison_with_nan
      (machine_width : Target_system.Machine_width.t) (op : P.comparison unit)
      : M (binary_arith_outcome_for_one_side_only Target_ocaml_int.t) :=
    match op with
    | P.Neq =>
      let! tmp1 := Target_ocaml_int.bool_true machine_width in
      ret (Exactly tmp1)
    | P.Eq | P.Lt tt | P.Gt tt | P.Le tt | P.Ge tt =>
      let! tmp1 := Target_ocaml_int.bool_false machine_width in
      ret (Exactly tmp1)
    end.

  (* 943-950. In the compiler: [~machine_width op ~rhs]. *)
  Definition op_lhs_unknown (machine_width : Target_system.Machine_width.t)
      (op : op_) (rhs : F.t)
      : M (binary_arith_outcome_for_one_side_only Target_ocaml_int.t) :=
    match op with
    | P.Yielding_bool op =>
      let! tmp1 := F.is_any_nan rhs in
      if tmp1
      then result_of_comparison_with_nan machine_width op
      else ret Cannot_simplify
    | P.Yielding_int_like_compare_functions tt => ret Cannot_simplify
    end.

  (* 952-959. In the compiler: [~machine_width op ~lhs]. *)
  Definition op_rhs_unknown (machine_width : Target_system.Machine_width.t)
      (op : op_) (lhs : F.t)
      : M (binary_arith_outcome_for_one_side_only Target_ocaml_int.t) :=
    match op with
    | P.Yielding_bool op =>
      let! tmp1 := F.is_any_nan lhs in
      if tmp1
      then result_of_comparison_with_nan machine_width op
      else ret Cannot_simplify
    | P.Yielding_int_like_compare_functions tt => ret Cannot_simplify
    end.
End Float_ops_for_binary_comp_gen.

(* 962-968 *)
(* PORT-GAP(loose): 962-976, the argument of each application, which the
   compiler writes in place, is a module with a name. *)
Module Float_ops_for_binary_comp_FP.
  Module F := Float_by_bit_pattern.

  Definition arg_kind : K.Standard_int_or_float.t :=
    K.Standard_int_or_float.Naked_float.

  Definition prover := T.meet_naked_floats.
End Float_ops_for_binary_comp_FP.

Module Float_ops_for_binary_comp :=
  Float_ops_for_binary_comp_gen (Float_ops_for_binary_comp_FP).

(* 970-976 *)
Module Float32_ops_for_binary_comp_FP.
  Module F := Float32_by_bit_pattern.

  Definition arg_kind : K.Standard_int_or_float.t :=
    K.Standard_int_or_float.Naked_float32.

  Definition prover := T.meet_naked_float32s.
End Float32_ops_for_binary_comp_FP.

Module Float32_ops_for_binary_comp :=
  Float_ops_for_binary_comp_gen (Float32_ops_for_binary_comp_FP).

(* 978-979 *)
Module Binary_float_comp := Binary_arith_like (Float_ops_for_binary_comp).
Module Binary_float32_comp := Binary_arith_like (Float32_ops_for_binary_comp).

(* 981-983: Unlike in the language specification, the compiler defines
   physical equality as referential equality on all values, including
   immediates and immutable blocks. *)
(* 984-1007. In the compiler: [op dacc ~original_term _dbg ~arg1:_ ~arg1_ty
   ~arg2:_ ~arg2_ty ~result_var]. *)
Definition simplify_phys_equal (op : P.equality_comparison) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t)
    (arg1_ty : T.t) (_ : Simple.t) (arg2_ty : T.t) (result_var : Bound_var.t)
    : M SPR.t :=
  (* This primitive is only used for arguments of kind [Value]. *)
  let* typing_env := DA.typing_env dacc in
  (* Note: We don't compare the arguments themselves for equality. Instead, we
     know that [simplify_simple] always returns alias types, so we let the
     prover do the matching. *)
  let* machine_width :=
    let! tmp1 := DA.denv dacc in
    DE.machine_width tmp1
  in
  let! tmp1 := T.prove_physical_equality typing_env arg1_ty arg2_ty in
  match tmp1 with
  | T.Proved bool =>
    let& result := match op with P.Eq_ => bool | P.Neq_ => negb bool end in
    let* dacc :=
      let! tmp2 := Target_ocaml_int.bool_ machine_width result in
      let! tmp3 := T.this_naked_immediate tmp2 in
      DA.add_variable dacc result_var tmp3
    in
    let! tmp4 := Simple.untagged_const_bool machine_width result in
    let! tmp5 := Named.create_simple tmp4 in
    SPR.create tmp5 false dacc
  | T.Unknown =>
    let* dacc :=
      let! tmp2 := Target_ocaml_int.all_bools machine_width in
      let! tmp3 := T.these_naked_immediates tmp2 in
      DA.add_variable dacc result_var tmp3
    in
    SPR.create original_term false dacc
  end.

(* 1009-1080. In the compiler: [array_kind array_load_kind mutability dacc
   ~original_term:_ dbg ~arg1:array ~arg1_ty:array_ty ~arg2:index
   ~arg2_ty:index_ty ~result_var]. *)
Definition simplify_array_load (array_kind : P.Array_kind.t)
    (array_load_kind : P.Array_load_kind.t) (mutability : Mutability.t)
    (dacc : DA.t) (_ : Named.t) (dbg : Debuginfo.t) (array : Simple.t)
    (array_ty : T.t) (index : Simple.t) (index_ty : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let& result_kind :=
    match array_load_kind with
    | P.Array_load_kind.Immediates => K.value
    | P.Array_load_kind.Gc_ignorable_values | P.Array_load_kind.Values =>
      K.value
    | P.Array_load_kind.Naked_floats => K.naked_float
    | P.Array_load_kind.Naked_float32s => K.naked_float32
    | P.Array_load_kind.Naked_ints => K.naked_immediate
    | P.Array_load_kind.Naked_int8s => K.naked_int8
    | P.Array_load_kind.Naked_int16s => K.naked_int16
    | P.Array_load_kind.Naked_int32s => K.naked_int32
    | P.Array_load_kind.Naked_int64s => K.naked_int64
    | P.Array_load_kind.Naked_nativeints => K.naked_nativeint
    | P.Array_load_kind.Naked_vec128s => K.naked_vec128
    | P.Array_load_kind.Naked_vec256s => K.naked_vec256
    | P.Array_load_kind.Naked_vec512s => K.naked_vec512
    | P.Array_load_kind.Naked_masks => K.naked_mask
    end
  in
  let* array_kind :=
    Simplify_common.specialise_array_kind dacc array_kind array_ty
  in
  match array_kind with
  | Or_bottom.Bottom =>
    let* ty := T.bottom result_kind in
    let* dacc := DA.add_variable dacc result_var ty in
    SPR.create_invalid dacc
  | Or_bottom.Ok array_kind =>
    let& prim :=
      P.Binary (P.Array_load array_kind array_load_kind mutability) array index
    in
    (* PORT-GAP(loose): 1042, the attribute [@inline] is not kept. *)
    let& return_given_type :=
      fun (ty : T.t) (try_reify : bool) =>
      let* named := Named.create_prim prim dbg in
      let* dacc := DA.add_variable dacc result_var ty in
      SPR.create named try_reify dacc
    in
    (* PORT-GAP(loose): 1047, the attribute [@inline] is not kept. *)
    let& contents_unknown :=
      fun (_ : unit) =>
      let! tmp1 := P.result_kind' prim in
      let! tmp2 := T.unknown tmp1 in
      return_given_type tmp2 false
    in
    let! tmp1 := DA.typing_env dacc in
    let! tmp2 := T.prove_is_immutable_array tmp1 array_ty in
    match tmp2 with
    | T.Unknown => contents_unknown tt
    | T.Proved (T3 elt_kind fields _mode) =>
      match elt_kind with
      | Or_unknown_or_bottom.Unknown | Or_unknown_or_bottom.Bottom =>
        contents_unknown tt
      | Or_unknown_or_bottom.Ok elt_kind =>
        let! tmp3 := K.With_subkind.kind elt_kind in
        let! tmp4 := K.equal tmp3 result_kind in
        if negb tmp4
        then contents_unknown tt
        else
          let! tmp5 := DA.typing_env dacc in
          let! tmp6 := T.prove_equals_tagged_immediates tmp5 index_ty in
          match tmp6 with
          | T.Unknown => contents_unknown tt
          | T.Proved imms =>
            let! tmp7 := Target_ocaml_int.Set_.get_singleton imms in
            match tmp7 with
            | None => contents_unknown tt
            | Some imm =>
              let* machine_width :=
                let! tmp8 := DA.denv dacc in
                DE.machine_width tmp8
              in
              (* 1070-1074: [Array.length fields |> Target_ocaml_int.of_int
                 machine_width] is [Target_ocaml_int.of_int machine_width
                 (Array.length fields)]. *)
              let! tmp9 := Target_ocaml_int.zero machine_width in
              let! tmp10 := Target_ocaml_int.op_lt imm tmp9 in
              let! tmp11 :=
                or_else tmp10
                  (let! tmp12 := Array.length fields in
                   let! tmp13 := Target_ocaml_int.of_int machine_width tmp12 in
                   Target_ocaml_int.op_gt_eq imm tmp13)
              in
              if tmp11
              then SPR.create_invalid dacc
              else
                (* 1078: [fields.(i)] is [Array.get fields i]. *)
                let! tmp14 := Target_ocaml_int.to_int imm in
                let! tmp15 := Array.get fields tmp14 in
                return_given_type tmp15 true
            end
          end
      end
    end
  end.

(* 1082-1088. In the compiler: [_string_like_value _string_accessor_width
   ~original_prim dacc ~original_term _dbg ~arg1:_ ~arg1_ty:_ ~arg2:_
   ~arg2_ty:_ ~result_var]. 1086-1088, [SPR.create_unknown dacc ~result_var
   kind ~original_term]: the arguments are in the order of the interface. *)
Definition simplify_string_or_bigstring_load
    (_string_like_value : P.string_like_value)
    (_string_accessor_width : P.string_accessor_width) (original_prim : P.t)
    (dacc : DA.t) (original_term : Named.t) (_dbg : Debuginfo.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1090-1095 *)
Definition simplify_bigarray_load (_num_dimensions : P.num_dimensions)
    (_bigarray_kind : P.Bigarray_kind.t)
    (_bigarray_layout : P.Bigarray_layout.t) (original_prim : P.t)
    (dacc : DA.t) (original_term : Named.t) (_dbg : Debuginfo.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1097-1101 *)
Definition simplify_bigarray_get_alignment (_align : int)
    (original_prim : P.t) (dacc : DA.t) (original_term : Named.t)
    (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1103-1107 *)
Definition simplify_atomic_load (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1109-1111. In the compiler: [_block_access_kind _init_or_assign ~field:_
   dacc ~original_term _dbg ~arg1:_ ~arg1_ty:_ ~arg2:_ ~arg2_ty:_
   ~result_var]. *)
Definition simplify_block_set (_block_access_kind : P.Block_access_kind.t)
    (_init_or_assign : P.Init_or_assign.t) (_ : Target_ocaml_int.t)
    (dacc : DA.t) (original_term : Named.t) (_dbg : Debuginfo.t)
    (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unit dacc result_var original_term.

(* 1113-1115 *)
Definition simplify_poke (dacc : DA.t) (original_term : Named.t)
    (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t) (_ : Simple.t) (_ : T.t)
    (result_var : Bound_var.t) : M SPR.t :=
  SPR.create_unit dacc result_var original_term.

(* 1117-1121 *)
Definition simplify_read_offset (original_prim : P.t) (dacc : DA.t)
    (original_term : Named.t) (_dbg : Debuginfo.t) (_ : Simple.t) (_ : T.t)
    (_ : Simple.t) (_ : T.t) (result_var : Bound_var.t) : M SPR.t :=
  let! tmp1 := P.result_kind' original_prim in
  SPR.create_unknown dacc result_var tmp1 original_term.

(* 1123-1179. In the compiler: [dacc original_prim prim ~arg1 ~arg1_ty ~arg2
   ~arg2_ty dbg ~result_var]. *)
Definition simplify_binary_primitive0 (dacc : DA.t) (original_prim : P.t)
    (prim : P.binary_primitive) (arg1 : Simple.t) (arg1_ty : T.t)
    (arg2 : Simple.t) (arg2_ty : T.t) (dbg : Debuginfo.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* original_term := Named.create_prim original_prim dbg in
  (* 1126-1177: a function given its first arguments is a value. *)
  let& simplifier :=
    match prim with
    | P.Block_set kind init field => simplify_block_set kind init field
    | P.Array_load array_kind width mutability =>
      simplify_array_load array_kind width mutability
    | P.Int_arith_ kind op =>
      match kind with
      | K.Standard_int.Tagged_immediate =>
        Binary_int_arith_tagged_immediate.simplify op
      | K.Standard_int.Naked_immediate =>
        Binary_int_arith_naked_immediate.simplify op
      | K.Standard_int.Naked_int8 => Binary_int_arith_int8.simplify op
      | K.Standard_int.Naked_int16 => Binary_int_arith_int16.simplify op
      | K.Standard_int.Naked_int32 => Binary_int_arith_int32.simplify op
      | K.Standard_int.Naked_int64 => Binary_int_arith_int64.simplify op
      | K.Standard_int.Naked_nativeint => Binary_int_arith_nativeint.simplify op
      end
    | P.Int_shift kind op =>
      match kind with
      | K.Standard_int.Tagged_immediate =>
        Binary_int_shift_tagged_immediate.simplify op
      | K.Standard_int.Naked_immediate =>
        Binary_int_shift_naked_immediate.simplify op
      | K.Standard_int.Naked_int8 => Binary_int_shift_int8.simplify op
      | K.Standard_int.Naked_int16 => Binary_int_shift_int16.simplify op
      | K.Standard_int.Naked_int32 => Binary_int_shift_int32.simplify op
      | K.Standard_int.Naked_int64 => Binary_int_shift_int64.simplify op
      | K.Standard_int.Naked_nativeint => Binary_int_shift_nativeint.simplify op
      end
    | P.Int_comp kind op =>
      match kind with
      | K.Standard_int.Tagged_immediate =>
        Binary_int_comp_tagged_immediate.simplify op
      | K.Standard_int.Naked_immediate =>
        Binary_int_comp_naked_immediate.simplify op
      | K.Standard_int.Naked_int8 => Binary_int_comp_int8.simplify op
      | K.Standard_int.Naked_int16 => Binary_int_comp_int16.simplify op
      | K.Standard_int.Naked_int32 => Binary_int_comp_int32.simplify op
      | K.Standard_int.Naked_int64 => Binary_int_comp_int64.simplify op
      | K.Standard_int.Naked_nativeint => Binary_int_comp_nativeint.simplify op
      end
    | P.Float_arith_ P.Float64 op => Binary_float_arith.simplify op
    | P.Float_comp P.Float64 op => Binary_float_comp.simplify op
    (* Note: despite the fact that all float32s are representable as float64s,
       float32 arithmetic operations need to be performed in 32-bit precision to
       preserve rounding behavior. Such 32-bit operations are implemented by
       flambda2_floats. *)
    | P.Float_arith_ P.Float32 op => Binary_float32_arith.simplify op
    | P.Float_comp P.Float32 op => Binary_float32_comp.simplify op
    | P.Phys_equal op => simplify_phys_equal op
    | P.String_or_bigstring_load string_like_value string_accessor_width =>
      simplify_string_or_bigstring_load string_like_value
        string_accessor_width original_prim
    | P.Bigarray_load num_dimensions bigarray_kind bigarray_layout =>
      simplify_bigarray_load num_dimensions bigarray_kind bigarray_layout
        original_prim
    | P.Bigarray_get_alignment align =>
      simplify_bigarray_get_alignment align original_prim
    | P.Atomic_load _ _ => simplify_atomic_load original_prim
    | P.Poke _ => simplify_poke
    | P.Read_offset _ _ => simplify_read_offset original_prim
    end
  in
  simplifier dacc original_term dbg arg1 arg1_ty arg2 arg2_ty result_var.

(* 1181-1239. In the compiler: [dacc prim ~arg1 ~arg2]. *)
Definition recover_comparison_primitive (dacc : DA.t)
    (prim : P.binary_primitive) (arg1 arg2 : Simple.t) : M (option P.t) :=
  let& try_one_direction :=
    fun (left right : Simple.t) (op : P.comparison P.signed_or_unsigned) =>
    Simple.pattern_match right
      (fun _ _ => ret None)
      (fun const =>
        (* PORT-GAP(loose): 1186, the attribute [@warning "-fragile-match"]
           is not kept. *)
        let! tmp1 := Const.descr const in
        match tmp1 with
        | Int_ids.Const.Descr.Tagged_immediate i =>
          (* 1188-1189: [when Target_ocaml_int.(equal i (zero (DE.machine_width
             (DA.denv dacc))))] *)
          let! tmp2 := DA.denv dacc in
          let! tmp3 := DE.machine_width tmp2 in
          let! tmp4 := Target_ocaml_int.zero tmp3 in
          let! tmp5 := Target_ocaml_int.equal i tmp4 in
          if tmp5
          then
            (* 1190-1198, [Simple.pattern_match' left ~const ~symbol ~var]:
               the arguments are in the order of the interface. *)
            Simple.pattern_match' left
              (fun var _ =>
                let! tmp6 := DA.denv dacc in
                let! tmp7 := DE.find_comparison_result tmp6 var in
                match tmp7 with
                | None => ret None
                | Some comp =>
                  Comparison_result.convert_result_compared_to_tagged_zero comp
                    op
                end)
              (fun _ _ => ret None)
              (fun _ => ret None)
          else ret None
        | _ => ret None
        end)
  in
  let& try_both_directions :=
    fun (op swapped_op : P.comparison P.signed_or_unsigned) =>
    let! tmp1 := try_one_direction arg1 arg2 op in
    match tmp1 with
    | Some p => ret (Some p)
    | None => try_one_direction arg2 arg1 swapped_op
    end
  in
  match prim with
  | P.Block_set _ _ _ | P.Array_load _ _ _ | P.Int_arith_ _ _ | P.Int_shift _ _
  | P.Int_comp _ (P.Yielding_int_like_compare_functions _)
  | P.Float_arith_ _ _ | P.Float_comp _ _ | P.String_or_bigstring_load _ _
  | P.Bigarray_load _ _ _ | P.Bigarray_get_alignment _ | P.Atomic_load _ _
  | P.Poke _ | P.Read_offset _ _ =>
    ret None
  | P.Phys_equal op =>
    (* Integer (in)equality reaches Flambda2 as [Phys_equal] (cf.
       [Lambda_to_flambda_primitives]), so this is the form taken by e.g.
       [compare x y = 0]. The result of a comparison is always a tagged
       immediate, for which physical equality is value equality, so it collapses
       like [Int_comp] equality does. *)
    let& op :=
      (match op with P.Eq_ => P.Eq | P.Neq_ => P.Neq end
        : P.comparison P.signed_or_unsigned)
    in
    try_both_directions op op
  | P.Int_comp kind (P.Yielding_bool op) =>
    match kind with
    | K.Standard_int.Naked_immediate | K.Standard_int.Naked_int8
    | K.Standard_int.Naked_int16 | K.Standard_int.Naked_int32
    | K.Standard_int.Naked_int64 | K.Standard_int.Naked_nativeint =>
      ret None
    | K.Standard_int.Tagged_immediate =>
      let& swapped_op :=
        match op with
        | P.Eq => P.Eq
        | P.Neq => P.Neq
        (* Note that this is not handling a negation of an inequality, it is
           simply a pattern match for when the inequality appears the other way
           around. So e.g. [Lt] maps to [Gt], not [Ge]. *)
        | P.Lt s => P.Gt s
        | P.Gt s => P.Lt s
        | P.Le s => P.Ge s
        | P.Ge s => P.Le s
        end
      in
      try_both_directions op swapped_op
    end
  end.

(* 1241-1270. In the compiler: [dacc original_prim prim ~arg1 ~arg1_ty ~arg2
   ~arg2_ty dbg ~result_var]. *)
Definition simplify_binary_primitive (dacc : DA.t) (original_prim : P.t)
    (prim : P.binary_primitive) (arg1 : Simple.t) (arg1_ty : T.t)
    (arg2 : Simple.t) (arg2_ty : T.t) (dbg : Debuginfo.t)
    (result_var : Bound_var.t) : M SPR.t :=
  let* '(T6 original_prim prim arg1 arg1_ty arg2 arg2_ty) :=
    (* PORT-GAP(loose): 1244, the attribute [@warning "-fragile-match"] is
       not kept. *)
    let! tmp1 := recover_comparison_primitive dacc prim arg1 arg2 in
    match tmp1 with
    | None => ret (T6 original_prim prim arg1 arg1_ty arg2 arg2_ty)
    | Some (P.Binary new_prim new_arg1 new_arg2 as new_original_prim) =>
      let* min_name_mode := Bound_var.name_mode result_var in
      let* arg1_ty_opt :=
        S.simplify_simple_if_in_scope dacc new_arg1 min_name_mode
      in
      let* arg2_ty_opt :=
        S.simplify_simple_if_in_scope dacc new_arg2 min_name_mode
      in
      match arg1_ty_opt, arg2_ty_opt with
      | Some new_arg1_ty, Some new_arg2_ty =>
        ret
          (T6 new_original_prim new_prim new_arg1 new_arg1_ty new_arg2
             new_arg2_ty)
      | None, _ | _, None =>
        ret (T6 original_prim prim arg1 arg1_ty arg2 arg2_ty)
      end
    | Some other_prim =>
      fatal_errorf2 "Recovered primitive %a is not a comparison"
        Flambda_primitive.print other_prim
    end
  in
  simplify_binary_primitive0 dacc original_prim prim arg1 arg1_ty arg2 arg2_ty
    dbg result_var.
