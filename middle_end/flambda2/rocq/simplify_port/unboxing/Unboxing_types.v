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

(* This file follows middle_end/flambda2/simplify/unboxing/unboxing_types.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by
   definition under the compiler's names; the numbers in the comments are
   the lines of that file. What is not from that file: the form (the monad,
   the temporaries [tmpN] and their order, the fuel of the recursive
   functions) is that of GUIDE.md; the Rocq declarations of the types that
   have an inline record are in the form of decl/Unboxing_types.v. No
   proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter
  Flambda_debug_uid Flambda_kind Format Function_slot Tag Value_slot
  Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17 *)
(*OCAML
open! Simplify_import
OCAML*)

(* 19-29 *)
Inductive do_not_unbox_reason : Type :=
| Not_beneficial
| Max_depth_exceeded
| Incomplete_parameter_type
| Not_enough_information_at_use
| Not_of_kind_value
| Unboxing_not_requested
| All_fields_invalid.

(* 31-56 *)
Module Extra_param_and_args.
  (* 32-36 *)
  Record t : Type :=
    { param : Variable_.t;
      param_debug_uid : Flambda_debug_uid.t;
      args : Apply_cont_rewrite_id.Map.t EPA.Extra_arg.t
    }.

  (* 38-42 *)
  Definition create (name : string) (debug_uid : Flambda_debug_uid.t)
      (kind : Flambda_kind.t) : M t :=
    let! tmp1 := Variable_.create None name kind in
    ret
      {| param := tmp1;
         param_debug_uid := debug_uid;
         args := Apply_cont_rewrite_id.Map.empty
      |}.

  (* 47. [{ t with args }]. *)
  Definition update_args (t : Extra_param_and_args.t)
      (args : Apply_cont_rewrite_id.Map.t EPA.Extra_arg.t)
      : Extra_param_and_args.t :=
    {| param := t.(param);
       param_debug_uid := t.(param_debug_uid);
       args := args
    |}.
  Extract Inlined Constant update_args =>
  "(fun t args -> { t with args = args })".

  (* 44-47 *)
  Definition update_param_args (t : Extra_param_and_args.t)
      (rewrite_id : Apply_cont_rewrite_id.t) (extra_arg : EPA.Extra_arg.t)
      : M Extra_param_and_args.t :=
    (let! tmp1 := Apply_cont_rewrite_id.Map.mem rewrite_id t.(args) in
     assert_ (negb tmp1)) ;;
    let* args := Apply_cont_rewrite_id.Map.add rewrite_id extra_arg t.(args) in
    ret (update_args t args).

  (* 49-55 *)
  Definition print (fmt : Format.formatter)
      '({| param := param; param_debug_uid := _; args := _ |}
        : Extra_param_and_args.t) : M unit :=
    Format.fprintf2 fmt
      "@[<hv 1>(@[<hov>(param %a)@]@ @[<v 2>(args@ <...>)@])@]"
      Variable_.print param.
  (* (Apply_cont_rewrite_id.Map.print EPA.Extra_arg.print) args *)
End Extra_param_and_args.

(* 58-91 *)
(* PORT-GAP(type): the four types that the compiler defines together have
   inline records and a record that is recursive with the variants. As in
   decl/Unboxing_types.v: [field_decision] is abstract, with its maker
   [mk_field_decision] and its eliminator [match_field_decision]; the three
   variants take the fields of their inline records by place; [decision]
   is [decision_] in Rocq. *)
(* PORT-GAP(verbatim): the OCaml definition of the four types is the text of
   the directive of [field_decision]: Rocq prints it where the types are
   defined, after the types that it needs. It begins with [field_decision],
   which the compiler has in the second place. *)
Parameter field_decision : Type.
Extract Constant field_decision =>
  "{ epa : Extra_param_and_args.t;
    decision : decision;
    kind : Flambda_kind.With_subkind.t
  }

and unboxing_decision =
  | Unique_tag_and_size of
      { tag : Tag.t;
        shape : K.Block_shape.t;
        fields : field_decision list
      }
  | Variant of
      { tag : Extra_param_and_args.t;
        const_ctors : const_ctors_decision;
        fields_by_tag :
          (K.Block_shape.t * field_decision list) Tag.Scannable.Map.t
      }
  | Closure_single_entry of
      { function_slot : Function_slot.t;
        vars_within_closure : field_decision Value_slot.Map.t
      }
  | Number of Flambda_kind.Naked_number_kind.t * Extra_param_and_args.t

and const_ctors_decision =
  | Zero
  | At_least_one of
      { is_int : Extra_param_and_args.t;
        ctor : decision
      }

and decision =
  | Unbox of unboxing_decision
  | Do_not_unbox of do_not_unbox_reason".

Inductive unboxing_decision : Type :=
| Unique_tag_and_size :
    Tag.t -> Flambda_kind.Block_shape.t -> list field_decision ->
    unboxing_decision
| Variant :
    Extra_param_and_args.t -> const_ctors_decision ->
    Tag.Scannable.Map.t (Flambda_kind.Block_shape.t * list field_decision) ->
    unboxing_decision
| Closure_single_entry :
    Function_slot.t -> Value_slot.Map.t field_decision -> unboxing_decision
| Number :
    Flambda_kind.Naked_number_kind.t -> Extra_param_and_args.t ->
    unboxing_decision
with const_ctors_decision : Type :=
| Zero : const_ctors_decision
| At_least_one : Extra_param_and_args.t -> decision_ -> const_ctors_decision
with decision_ : Type :=
| Unbox : unboxing_decision -> decision_
| Do_not_unbox : do_not_unbox_reason -> decision_.
Extract Inductive unboxing_decision => "unboxing_decision" [ "(fun (x__1, x__2, x__3) -> (Unique_tag_and_size { tag = x__1; shape = x__2; fields = x__3 } : unboxing_decision))" "(fun (x__1, x__2, x__3) -> (Variant { tag = x__1; const_ctors = x__2; fields_by_tag = x__3 } : unboxing_decision))" "(fun (x__1, x__2) -> (Closure_single_entry { function_slot = x__1; vars_within_closure = x__2 } : unboxing_decision))" "Number" ] "(fun f__1 f__2 f__3 f__4 x__0 -> match (x__0 : unboxing_decision) with Unique_tag_and_size { tag = x__1; shape = x__2; fields = x__3 } -> f__1 x__1 x__2 x__3 | Variant { tag = x__1; const_ctors = x__2; fields_by_tag = x__3 } -> f__2 x__1 x__2 x__3 | Closure_single_entry { function_slot = x__1; vars_within_closure = x__2 } -> f__3 x__1 x__2 | Number (x__1, x__2) -> f__4 x__1 x__2)".
Extract Inductive const_ctors_decision => "const_ctors_decision" [ "Zero" "(fun (x__1, x__2) -> (At_least_one { is_int = x__1; ctor = x__2 } : const_ctors_decision))" ] "(fun f__1 f__2 x__0 -> match (x__0 : const_ctors_decision) with Zero -> f__1 () | At_least_one { is_int = x__1; ctor = x__2 } -> f__2 x__1 x__2)".
Extract Inductive decision_ => "decision" [ "Unbox" "Do_not_unbox" ].
Parameter mk_field_decision :
  Extra_param_and_args.t -> decision_ -> Flambda_kind.With_subkind.t ->
  field_decision.
Extract Inlined Constant mk_field_decision => "(fun x__1 x__2 x__3 -> { epa = x__1; decision = x__2; kind = x__3 })".
Parameter match_field_decision :
  forall {Res : Type},
  field_decision ->
  (Extra_param_and_args.t -> decision_ -> Flambda_kind.With_subkind.t ->
   M Res) ->
  M Res.
Extract Inlined Constant match_field_decision => "(fun x__0 f__1 -> let { epa = x__1; decision = x__2; kind = x__3 } = x__0 in f__1 x__1 x__2 x__3)".

(* 93-97. The type has the name of its first field: it is [decisions_]. *)
Record decisions_ : Type :=
  { decisions : list (BP.t * decision_);
    rewrite_ids_seen : Apply_cont_rewrite_id.Set_.t;
    rewrites_ids_known_as_invalid : Apply_cont_rewrite_id.Set_.t
  }.

(* 99-101 *)
Inductive pass : Type :=
| Filter
| Compute_all_extra_args.

(* Printing *)
(* ******** *)

(* 106-114 *)
Definition print_do_not_unbox_reason (ppf : Format.formatter)
    (reason : do_not_unbox_reason) : M unit :=
  match reason with
  | Not_beneficial => Format.fprintf0 ppf "not_beneficial"
  | Max_depth_exceeded => Format.fprintf0 ppf "max_depth_exceeded"
  | Incomplete_parameter_type =>
    Format.fprintf0 ppf "incomplete_parameter_type"
  | Not_enough_information_at_use =>
    Format.fprintf0 ppf "not_enough_information_at_use"
  | Not_of_kind_value => Format.fprintf0 ppf "not_of_kind_value"
  | Unboxing_not_requested => Format.fprintf0 ppf "unboxing_not_requested"
  | All_fields_invalid => Format.fprintf0 ppf "all_fields_invalid"
  end.

(* 116-142 *)
Fixpoint print_decision (fuel : fuel) (ppf : Format.formatter)
    (decision : decision_) {struct fuel} : M unit :=
  recursive! fuel in
  match decision with
  | Do_not_unbox reason =>
    Format.fprintf2 ppf "@[<hov 1>(do_not_unbox@ %a)@]"
      print_do_not_unbox_reason reason
  | Unbox (Unique_tag_and_size tag shape fields) =>
    let! tmp1 := papp1 print_fields_decisions fuel in
    Format.fprintf6 ppf
      "@[<v 1>(unique_tag_and_size@ @[<h>(static_tag %a)@]@ @[<h>(shape %a)@]@ @[<hv 2>(fields@ %a)@])@]"
      Tag.print tag K.Block_shape.print shape tmp1 fields
  | Unbox (Variant tag const_ctors fields_by_tag) =>
    let! tmp1 :=
      papp1 Tag.Scannable.Map.print
        (fun (ppf : Format.formatter)
             '((_shape, fields) : K.Block_shape.t * list field_decision) =>
          print_fields_decisions fuel ppf fields)
    in
    let! tmp2 := papp1 print_const_ctor_num fuel in
    Format.fprintf6 ppf
      "@[<v 2>(variant@ @[<hov>(tag %a)@]@ @[<hv 2>(const_ctors@ %a)@]@ @[<v 2>(fields_by_tag@ %a)@])@]"
      Extra_param_and_args.print tag tmp2 const_ctors tmp1 fields_by_tag
  | Unbox (Closure_single_entry function_slot vars_within_closure) =>
    let! tmp1 := papp1 print_field_decision fuel in
    let! tmp2 := papp1 Value_slot.Map.print tmp1 in
    Format.fprintf4 ppf
      "@[<hov 1>(closure_single_entry@ @[<hov>(function_slot@ %a)@]@ @[<hv 2>(value_slots@ %a)@])@]"
      Function_slot.print function_slot tmp2 vars_within_closure
  | Unbox (Number kind epa) =>
    Format.fprintf4 ppf
      "@[<hv 1>(number@ @[<h>(kind %a)@]@ @[<hv 1>(var %a)@])@]"
      Flambda_kind.Naked_number_kind.print kind Extra_param_and_args.print epa
  end

(* 144-148 *)
with print_field_decision (fuel : fuel) (ppf : Format.formatter)
    (field_decision : field_decision) {struct fuel} : M unit :=
  recursive! fuel in
  match_field_decision field_decision (fun epa decision kind =>
    let! tmp1 := papp1 print_decision fuel in
    Format.fprintf6 ppf
      "@[<hv 1>(@,@[<hov 1>(var %a)@]@ @[<hv 1>(decision@ %a)@]@ (kind@ %a))@]"
      Extra_param_and_args.print epa tmp1 decision
      Flambda_kind.With_subkind.print kind)

(* 150-152 *)
with print_fields_decisions (fuel : fuel) (ppf : Format.formatter)
    (l : list field_decision) {struct fuel} : M unit :=
  recursive! fuel in
  let& pp_sep := Format.pp_print_space in
  let! tmp1 := papp1 print_field_decision fuel in
  let! tmp2 := papp2 Format.pp_print_list (Some pp_sep) tmp1 in
  Format.fprintf2 ppf "%a" tmp2 l

(* 154-160 *)
with print_const_ctor_num (fuel : fuel) (ppf : Format.formatter)
    (const_ctors : const_ctors_decision) {struct fuel} : M unit :=
  recursive! fuel in
  match const_ctors with
  | Zero => Format.fprintf0 ppf "no_const_ctors"
  | At_least_one is_int ctor =>
    let! tmp1 := papp1 print_decision fuel in
    Format.fprintf4 ppf
      "@[<hov 1>(const_ctors@ @[<hov 1>(is_int@ %a)@]@ @[<hov 1>(ctor@ %a)@])@]"
      Extra_param_and_args.print is_int tmp1 ctor
  end.

(* 162-176 *)
Definition print (ppf : Format.formatter)
    '({| decisions := decisions;
         rewrite_ids_seen := rewrite_ids_seen;
         rewrites_ids_known_as_invalid := rewrites_ids_known_as_invalid
      |}
      : decisions_) : M unit :=
  let& pp_sep := Format.pp_print_space in
  let& aux :=
    fun (ppf : Format.formatter) '((param, decision) : BP.t * decision_) =>
    let_fuel! fuel in
    let! tmp1 := papp1 print_decision fuel in
    Format.fprintf4 ppf "@[<hov 1>(%a@ %a)@]" BP.print param tmp1 decision
  in
  let! tmp1 := papp2 Format.pp_print_list (Some pp_sep) aux in
  Format.fprintf6 ppf
    "@[<hov 1>(@[<hov 1>(decisions@ %a)@]@ @[<hov 1>(rewrite_ids_seen@ %a)@]@ @[<hov 1>(rewrites_ids_known_as_invalid@ %a)@])@]"
    tmp1 decisions Apply_cont_rewrite_id.Set_.print rewrite_ids_seen
    Apply_cont_rewrite_id.Set_.print rewrites_ids_known_as_invalid.

(* 178-186 *)
Module Decisions.
  (* PORT-GAP(verbatim): 179-183, the compiler defines the record again,
     equal to [decisions]: the OCaml text is that of the directive. *)
  Definition t : Type := decisions_.
  Extract Constant t =>
    "decisions_ =
    { decisions : (BP.t * decision) list;
      rewrite_ids_seen : Apply_cont_rewrite_id.Set.t;
      rewrites_ids_known_as_invalid : Apply_cont_rewrite_id.Set.t
    }".

  (* 185 *)
  Definition print := print.
End Decisions.
