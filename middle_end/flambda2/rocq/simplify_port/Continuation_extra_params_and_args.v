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
   middle_end/flambda2/simplify/continuation_extra_params_and_args.ml
   (Git blob 5e2fbffe2d3a1f4aba19cf0fff6d855fdf950b59), function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md; the Rocq
   declarations of the module [Extra_arg] and of the type [t] have the form
   of decl/Continuation_extra_params_and_args.v. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter
  Bound_parameters Flambda_primitive Format List Or_invalid Simple Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 17-51. The module [Extra_arg] (its type, [print], [List.print]: lines
   17-44) and the type [t] (46-51) are the compiler's text. The type [t] has
   an inline record, so its OCaml definition must be verbatim, and verbatim
   text is at the head of the extracted file: what it mentions ([Extra_arg.t])
   must be there too. The two printers of [Extra_arg] are therefore not
   ported. *)
(*OCAML
module Extra_arg = struct
  type t =
    | Already_in_scope of Simple.t
    | New_let_binding of Variable.t * Flambda_primitive.t
    | New_let_binding_with_named_args of
        Variable.t * (Simple.t list -> Flambda_primitive.t)

  let [@ocamlformat "disable"] print ppf t =
    match t with
    | Already_in_scope simple ->
      Format.fprintf ppf "@[<hov 1>(Already_in_scope@ %a)@]"
        Simple.print simple
    | New_let_binding (var, prim) ->
      Format.fprintf ppf "@[<hov 1>(New_let_binding@ %a@ %a)@]"
        Variable.print var
        Flambda_primitive.print prim
    | New_let_binding_with_named_args (var, _) ->
      Format.fprintf ppf "@[<hov 1>(New_let_binding_with_named_args@ %a@ <fun>)@]"
        Variable.print var

  module List = struct
    type nonrec t = t list

    let [@ocamlformat "disable"] print ppf t =
      Format.fprintf ppf "(%a)"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space print) t
  end
end

type t =
  | Empty
  | Non_empty of
      { extra_params : Bound_parameters.t;
        extra_args : Extra_arg.t list Or_invalid.t Apply_cont_rewrite_id.Map.t
      }
OCAML*)

(* 17-44 *)
(* The declarations of the verbatim module [Extra_arg], in the form of decl/.
   They are not in a Rocq [Module]: Rocq would extract one, which would hide
   the verbatim module. [Extra_arg_t] is [Extra_arg.t], [Extra_arg_print] is
   [Extra_arg.print], [Extra_arg_List_print] is [Extra_arg.List.print]. *)
Inductive Extra_arg_t : Type :=
| Already_in_scope : Simple.t -> Extra_arg_t
| New_let_binding : Variable_.t -> Flambda_primitive.t -> Extra_arg_t
| New_let_binding_with_named_args :
    Variable_.t -> (list Simple.t -> M Flambda_primitive.t) -> Extra_arg_t.
Extract Inductive Extra_arg_t => "Extra_arg.t"
  [ "Extra_arg.Already_in_scope" "Extra_arg.New_let_binding"
    "Extra_arg.New_let_binding_with_named_args" ].
Parameter Extra_arg_print : Format.formatter -> Extra_arg_t -> M unit.
Extract Inlined Constant Extra_arg_print => "Extra_arg.print".
Parameter Extra_arg_List_print :
  Format.formatter -> list Extra_arg_t -> M unit.
Extract Inlined Constant Extra_arg_List_print => "Extra_arg.List.print".

(* 46-51 *)
(* The type has an inline record; the fields are by place, as in decl/. (The
   strings do not name the type [t]. When they were written, Rocq wrote
   [open Apply_cont_rewrite_id] after the verbatim text, and that module has
   a type [t] too; the extracted file has that line no more.) *)
Inductive t : Type :=
| Empty : t
| Non_empty :
    Bound_parameters.t ->
    Apply_cont_rewrite_id.Map.t (Or_invalid.t (list Extra_arg_t)) -> t.
Extract Inductive t => "t"
  [ "Empty"
    "(fun (x__1, x__2) -> Non_empty { extra_params = x__1; extra_args = x__2 })" ]
  "(fun f__1 f__2 x__0 -> match x__0 with Empty -> f__1 () | Non_empty { extra_params = x__1; extra_args = x__2 } -> f__2 x__1 x__2)".

(* 53-61 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept; the
   lines of the format are joined. *)
Definition print (ppf : Format.formatter) (t : t) : M unit :=
  match t with
  | Empty => Format.fprintf0 ppf "(empty)"
  | Non_empty extra_params extra_args =>
    (* 61 *)
    let! tmp1 := papp1 Or_invalid.print Extra_arg_List_print in
    let! tmp2 := papp1 Apply_cont_rewrite_id.Map.print tmp1 in
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(extra_params@ %a)@]@ @[<hov 1>(extra_args@ %a)@])@]"
      Bound_parameters.print extra_params tmp2 extra_args
  end.

(* 63 *)
Definition empty : t := Empty.

(* 65-68 *)
Definition is_empty (t : t) : M bool :=
  match t with
  | Empty => ret true
  | Non_empty _ extra_args => Apply_cont_rewrite_id.Map.is_empty extra_args
  end.

(* 70-134 *)
Definition add (t : t) (invalids : Apply_cont_rewrite_id.Set_.t)
    (extra_param : Bound_parameter.t)
    (extra_args : Apply_cont_rewrite_id.Map.t Extra_arg_t)
    : M Continuation_extra_params_and_args.t :=
  (* Note: there can be some overlap between the invalid ids and the keys of the
     [extra_args] map. This is notably used by the unboxing code which may
     compute some extra args and only later (when computing extra args for
     another parameter) realize that some rewrite ids are invalids, and then
     call this function with this new invalid set and the extra_args computed
     before this invalid set was known. *)
  match t with
  | Empty =>
    let* extra_params := Bound_parameters.create [extra_param] in
    let* valid_extra_args :=
      Apply_cont_rewrite_id.Map.map
        (fun extra_args => ret (Or_invalid.Ok [extra_args]))
        extra_args
    in
    let* extra_args :=
      Apply_cont_rewrite_id.Set_.fold
        (fun id map => Apply_cont_rewrite_id.Map.add id Or_invalid.Invalid map)
        invalids valid_extra_args
    in
    ret (Non_empty extra_params extra_args)
  | Non_empty extra_params already_extra_args =>
    let* extra_params := Bound_parameters.cons extra_param extra_params in
    let* extra_args :=
      Apply_cont_rewrite_id.Map.merge
        (fun id already_extra_args extra_arg =>
          (* The [invalids] set is expected to be small (actually, empty most of
             the time), so the lookups in each case of the merge should be
             reasonable, compared to merging (and allocating) the [invalids] set
             and the [extra_args] map. *)
          match already_extra_args, extra_arg with
          | None, None => ret None
          | None, Some _ =>
            (* 111 *)
            let! tmp1 := papp1 Apply_cont_rewrite_id.Map.print Extra_arg_print in
            fatal_errorf10
              "[Extra Params and Args] Unexpected New Apply_cont_rewrite_id (%a) for:
new param: %a
new args: %a
new invalids: %a
existing epa: %a"
              Apply_cont_rewrite_id.print id Bound_parameter.print extra_param
              tmp1 extra_args Apply_cont_rewrite_id.Set_.print invalids print t
          | Some _, None =>
            let! tmp1 := Apply_cont_rewrite_id.Set_.mem id invalids in
            if tmp1
            then ret (Some Or_invalid.Invalid)
            else
              (* 125 *)
              let! tmp2 :=
                papp1 Apply_cont_rewrite_id.Map.print Extra_arg_print
              in
              fatal_errorf10
                "[Extra Params and Args] Existing Apply_cont_rewrite_id (%a) missing for:
new param: %a
new args: %a
new invalids: %a
existing epa: %a"
                Apply_cont_rewrite_id.print id Bound_parameter.print
                extra_param tmp2 extra_args Apply_cont_rewrite_id.Set_.print
                invalids print t
          | Some Or_invalid.Invalid, Some _ => ret (Some Or_invalid.Invalid)
          | Some (Or_invalid.Ok already_extra_args), Some extra_arg =>
            let! tmp1 := Apply_cont_rewrite_id.Set_.mem id invalids in
            if tmp1
            then ret (Some Or_invalid.Invalid)
            else ret (Some (Or_invalid.Ok (extra_arg :: already_extra_args)))
          end)
        already_extra_args extra_args
    in
    ret (Non_empty extra_params extra_args)
  end.

(* 136-139 *)
Definition replace_extra_args (t : t)
    (extra_args :
      Apply_cont_rewrite_id.Map.t (Or_invalid.t (list Extra_arg_t)))
    : M Continuation_extra_params_and_args.t :=
  match t with
  | Empty => ret Empty
  | Non_empty extra_params _ => ret (Non_empty extra_params extra_args)
  end.

(* 141-168 *)
(* PORT-GAP(loose): 144, the compiler binds the two inline records as [t1]
   and [t2] and reads their fields; here the fields are bound by place,
   under the names [t1_extra_params], [t1_extra_args], [t2_extra_params],
   [t2_extra_args]. *)
Definition concat (outer inner : t) : M t :=
  match outer, inner with
  | Empty, t | t, Empty => ret t
  | Non_empty t1_extra_params t1_extra_args,
    Non_empty t2_extra_params t2_extra_args =>
    let* extra_args :=
      Apply_cont_rewrite_id.Map.merge
        (fun id extra_args1 extra_args2 =>
          match extra_args1, extra_args2 with
          | None, None => ret None
          | Some Or_invalid.Invalid, _ | _, Some Or_invalid.Invalid =>
            (* If either of [outer] or [inner] has proven that the use is
               invalid, that is enough -- the other case may have used that
               information to restrict the set of uses and hence not have extra
               args for that use. *)
            ret (Some Or_invalid.Invalid)
          | Some (Or_invalid.Ok _), None | None, Some (Or_invalid.Ok _) =>
            fatal_errorf6
              "concat: mismatching domains on id %a.@
outer: %a@
inner: %a"
              Apply_cont_rewrite_id.print id print outer print inner
          | Some (Or_invalid.Ok extra_args1), Some (Or_invalid.Ok extra_args2) =>
            ret (Some (Or_invalid.Ok (extra_args1 ++ extra_args2)%list))
          end)
        t1_extra_args t2_extra_args
    in
    let! tmp1 := Bound_parameters.append t1_extra_params t2_extra_params in
    ret (Non_empty tmp1 extra_args)
  end.

(* 170-172 *)
Definition extra_params (t : t) : M Bound_parameters.t :=
  match t with
  | Empty => ret Bound_parameters.empty
  | Non_empty extra_params _ => ret extra_params
  end.

(* 174-176 *)
Definition extra_args (t : t)
    : M (Apply_cont_rewrite_id.Map.t (Or_invalid.t (list Extra_arg_t))) :=
  match t with
  | Empty => ret Apply_cont_rewrite_id.Map.empty
  | Non_empty _ extra_args => ret extra_args
  end.

(* 178-179 *)
Definition init_with_params_only (extra_params : Bound_parameters.t) : M t :=
  ret (Non_empty extra_params Apply_cont_rewrite_id.Map.empty).

(* 181-198 *)
Definition add_args_for_all_params (t : t)
    (apply_cont_rewrite_id : Apply_cont_rewrite_id.t)
    (new_args : list Extra_arg_t)
    : M Continuation_extra_params_and_args.t :=
  let& error :=
    fun (_ : unit) =>
    (fatal_errorf0 "Mismatched number of extra params and extra args"
      : M Continuation_extra_params_and_args.t)
  in
  match t with
  | Empty =>
    match new_args with
    | [] => ret t
    | _ :: _ => error tt
    end
  | Non_empty extra_params extra_args =>
    let! tmp1 := Bound_parameters.to_list extra_params in
    let! tmp2 := List.compare_lengths new_args tmp1 in
    if negb (tmp2 =? 0)
    then error tt
    else
      let* extra_args :=
        Apply_cont_rewrite_id.Map.add apply_cont_rewrite_id
          (Or_invalid.Ok new_args) extra_args
      in
      ret (Non_empty extra_params extra_args)
  end.
