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

(* This file follows middle_end/flambda2/simplify/simplify_binary_primitive.ml
   (Git blob 2191c41d93f1b73603880e477f87e310995de46b), through the port's
   Simplify_binary_primitive.v, which follows that file. IT HOLDS COPIES OF
   FOUR LOCAL FUNCTIONS of [Binary_arith_like.simplify], with names, and the
   body of [simplify] with those names in it. It holds no statement and no
   proof.

   WHY. In the compiler, and so in the port, [result_unknown],
   [result_invalid], [check_possible_results] and [only_one_side_known] are
   local to [simplify]: the port's file exports no constant for any of
   them, so another file cannot name one. Here each has a name. Copies
   with a tie (below) are one sound way to state something of a local
   function; they are not the only way. Each copy is the port's text of
   the local function, line for line, with the variables of [simplify]
   that it uses as parameters before its own. The port's file is not
   changed.

   A COPY SAYS NOTHING BY ITSELF. WHAT TIES THESE TO THE PORT IS A
   THEOREM, which Rocq proves by computing: the port's [simplify] IS
   [simplify_with_named_locals] below, the body of [simplify] with the four
   copies where it has the four local functions
   ([simplify_is_its_named_locals]: its statement is in
   FlambdaPortIntArithInvalidSpec.v, its proof, [reflexivity], in
   FlambdaPortIntArithInvalidProofs.v). THE THEOREM IS AN EQUATION OF TWO
   COMPUTATIONS, NOT A COMPARISON OF TWO TEXTS: Rocq accepts it because
   it reduces the two sides to the same term. A change of a copy, or of
   the port's file, after which the two sides do not reduce to the same
   term makes that proof fail. A difference that Rocq reduces away does
   not: a comment, the name of a bound variable, a [let] that reduces
   away, another form that reduces to the same term. THAT THE LINES
   HERE ARE THE PORT'S LINES IS A SEPARATE CHECK: a reader compares
   them, and PROVENANCE.md says where they are from. No theorem says
   it.

   WHAT EACH DEFINITION IS A COPY OF: the lines of the port's
   Simplify_binary_primitive.v, then the lines of the compiler's file,
   then the variables of [simplify] that the local function uses, which
   are parameters of the copy before its own.

     [result_unknown]              474-480   143-149
        [denv], [op], [dacc], [result_var], [original_term]
     [result_invalid]              484-489   150-153
        [kind], [dacc], [result_var]
     [check_possible_results]      493-544   154-189
        [result_invalid], [original_term], [dbg], [kind], [denv], [op],
        [dacc], [result_var]
     [only_one_side_known]         556-645   190-240
        [denv], [check_possible_results], [result_unknown]
     [simplify_with_named_locals]  464-471 and 647-712   135-142 and 241-275
        the nine parameters of [simplify]

   WHAT IS NOT FROM THOSE LINES: the first lines of each definition (its
   name, and the variables of [simplify] that it uses, as parameters); in
   [simplify_with_named_locals], the lines that give the four local names
   to the four copies; the module around the definitions and its first
   three lines. The lines that this file requires are those of the port's
   file, and the port's file itself.

   THE COPIES ARE AT THE TAGGED IMMEDIATES, and not over any argument of
   the port's functor. In the port's lines [N] is the parameter of the
   functor [Binary_arith_like], and [Possible_result] is a type that the
   functor defines. ONE FORM OVER EVERY ARGUMENT WAS TRIED, AND IT
   FAILED: the copies in a functor of their own, which applies the
   port's functor once more to its argument. That application makes
   another type [Possible_result.t] than the port's module has, and the
   tie could not be proved by [reflexivity]. That is the failure of
   the form that was tried. It does not show that no form over every
   argument can be tied; no other was tried. Here [N] and [B] are the
   port's OWN two modules for the tagged immediates, under those two
   names: the lines are the port's, and they read as they do inside the
   port's functor at that argument. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Array Bound_var Comparison_result
  Container_types Debuginfo Int_ids List Mutability Number_adjuncts
  Numeric_types Or_bottom Or_unknown_or_bottom Reg_width_const Scalar Simple
  Simplify_common Target_ocaml_int Target_system.
From SimplifyPort.abbrev.simplify_binary_primitive Require Import Port_abbreviations.
From SimplifyPort Require Import Simplify_binary_primitive.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Module Tagged_immediate.

  (* [N]: the module that the port gives to [Binary_arith_like] for the
     tagged immediates. [B]: the port's module that the functor makes of
     it; its possible results, its sets of them and its [simplify] are
     those of the copies. *)
  Module N := Int_ops_for_binary_arith_tagged_immediate.
  Module B := Binary_int_arith_tagged_immediate.
  Import B.

  (* 143-149. The variables of [simplify]: [denv], [op], [dacc],
     [result_var], [original_term]. *)
  Definition result_unknown (denv : DE.t) (op : N.op_) (dacc : DA.t)
      (result_var : Bound_var.t) (original_term : Named.t) (_ : unit)
      : M SPR.t :=
    let* machine_width := DE.machine_width denv in
    let* dacc :=
      let! tmp1 := N.unknown machine_width op in
      DA.add_variable dacc result_var tmp1
    in
    SPR.create original_term false dacc.

  (* 150-153. The variables of [simplify]: [kind], [dacc],
     [result_var]. *)
  Definition result_invalid (kind : K.t) (dacc : DA.t)
      (result_var : Bound_var.t) (_ : unit) : M SPR.t :=
    let* dacc :=
      let! tmp1 := T.bottom kind in
      DA.add_variable dacc result_var tmp1
    in
    SPR.create_invalid dacc.

  (* 154-189. The variables of [simplify]: [result_invalid],
     [original_term], [dbg], [kind], [denv], [op], [dacc],
     [result_var]. *)
  Definition check_possible_results (result_invalid : unit -> M SPR.t)
      (original_term : Named.t) (dbg : Debuginfo.t) (kind : K.t)
      (denv : DE.t) (op : N.op_) (dacc : DA.t) (result_var : Bound_var.t)
      (possible_results : Possible_result.Set_.t) : M SPR.t :=
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
        (* 166, [is]: a word of Rocq, it gets one [_]. *)
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
      end.

  (* 190-240. The variables of [simplify]: [denv],
     [check_possible_results], [result_unknown]. The parameters after
     them are the local function's own. *)
  Definition only_one_side_known (denv : DE.t)
      (check_possible_results : Possible_result.Set_.t -> M SPR.t)
      (result_unknown : unit -> M SPR.t)
      (num nums_t : Type)
      (op : num -> M (binary_arith_outcome_for_one_side_only N.Result.t))
      (nums : nums_t)
      (folder :
        (num -> option Possible_result.Set_.t ->
         M (option Possible_result.Set_.t)) ->
        nums_t -> option Possible_result.Set_.t ->
        M (option Possible_result.Set_.t))
      (other_side : Simple.t) : M SPR.t :=
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
    end.

  (* 135-142 and 241-275: the body of [simplify], with the four copies
     where it has the four local functions. *)
  Definition simplify_with_named_locals (op : N.op_) (dacc : DA.t)
      (original_term : Named.t) (dbg : Debuginfo.t) (arg1 : Simple.t)
      (arg1_ty : T.t) (arg2 : Simple.t) (arg2_ty : T.t)
      (result_var : Bound_var.t) : M SPR.t :=
    let* denv := DA.denv dacc in
    let* typing_env := DE.typing_env denv in
    let* proof1 := N.prover_lhs typing_env arg1_ty in
    let* proof2 := N.prover_rhs typing_env arg2_ty in
    let& kind := N.result_kind in
    let& result_unknown :=
      result_unknown denv op dacc result_var original_term
    in
    let& result_invalid := result_invalid kind dacc result_var in
    let& check_possible_results :=
      check_possible_results result_invalid original_term dbg kind denv op
        dacc result_var
    in
    let only_one_side_known :=
      only_one_side_known denv check_possible_results result_unknown
    in
    (* 241-275: each of the first three cases has [when N.ok_to_evaluate
       denv]; where the answer is no, the case that follows them (273-274)
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

End Tagged_immediate.
