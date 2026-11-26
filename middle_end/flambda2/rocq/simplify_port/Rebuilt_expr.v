(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2021 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/rebuilt_expr.ml
   (Git blob d4549799a5871e659aab0a2992fcaea921fadc5c), function by function
   under the compiler's names; the numbers in the comments are the lines of that
   file. What is not from that file: the form (the monad, the temporaries [tmpN]
   and their order, the fuel of the recursive functions, the arguments by
   place) is that of GUIDE.md; the Rocq form of the types that Rocq cannot
   print (an inline record, a record with a mutable field) and the
   declarations marked PORT-GAP(decl) are written for this file. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Are_rebuilding_terms Bool
  Bound_parameter Bound_parameters Bound_pattern Bound_var Code_size Coercion
  Continuation Cost_metrics Flambda Flambda_features Flambda_kind
  Flambda_primitive Format Hashtbl List ListLabels Name Name_mode
  Name_occurrences Num_occurrences Numeric_types Option Or_null Or_unknown
  Recursive Reg_width_const Renaming Simple Switch_expr Symbol Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Bound_pattern.t Flambda.expr_descr Or_null.t
   Or_unknown.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* 15 *)
(*OCAML
open! Flambda.Import
OCAML*)
Import Flambda.Import_.
(* 16 *)
From SimplifyPort.abbrev.rebuilt_expr Require Import Port_abbreviations.
(*OCAML
module ART = Are_rebuilding_terms
OCAML*)
(* 354 and 390. [exception Match_failure] and [module HV = Hashtbl.Make
   (Variable)] are the compiler's lines; they stand at the head of the
   extracted file, not inside the modules [Matching_for_unique_handler] and
   [Match_permutable_parameters] (a verbatim block cannot stand inside a
   module). *)
(*OCAML
exception Match_failure

module HV = Hashtbl.Make (Variable)
OCAML*)

(* 18-21. The type has the name of a field of [t]: it gets one [_]. *)
Record contents_hash_ : Type :=
  { depth : int;
    structural_hash : int
  }.

(* 23-34 *)
Record t : Type :=
  { expr : Expr.t;
    is_cold : bool;
    contents_hash : Or_null.t contents_hash_
        (* If not null, this is a structural hash of the contents of this
           rebuilt expression (always null when not rebuilding terms).

           The hash should not depend on the name of variables within the
           expression, because we use it to de-duplicate continuation handlers
           that might bind variables with different names (see
           [Unique_continuation_map]). *)
  }.

(* 36 *)
(* PORT-GAP(loose): 36, [let is_cold { is_cold; _ } = is_cold] is the
   projection [is_cold] of the record [t] above (Rocq has one name space for
   fields and functions): Rocq extracts it as [let is_cold t = t.is_cold],
   after the type, and its Rocq type is not in the monad. *)

(* 38. [{ t with is_cold = true }]. *)
Definition update_is_cold (t : Rebuilt_expr.t) (is_cold : bool)
    : Rebuilt_expr.t :=
  {| expr := t.(expr);
     is_cold := is_cold;
     contents_hash := t.(contents_hash)
  |}.
Extract Inlined Constant update_is_cold =>
  "(fun t is_cold -> { t with is_cold = is_cold })".

(* 38 *)
Definition mark_as_cold (t : Rebuilt_expr.t) : M Rebuilt_expr.t :=
  ret (update_is_cold t true).

(* 40-54 *)
(* Rebuilt terms with no [contents_hash] cannot be deduplicated (e.g. because
   they contain not-shareable subterms such as sets of closures). We also want
   to clear it for terms that are "too big": sharing those is unlikely to
   succeed, and might cause hash collisions.

   This limit is added out of abundance of caution; it is likely fine to
   increase it or even remove it completely if needed (e.g. we end up having
   programs where we do want to share very large terms). Note that unlike the
   sharing of match branches in [lambda.ml] (which computes a sharing key with
   the same size as the term), there is no prohibitive memory cost to increasing
   this limit.

   The value of [32] matches [max_raw] in [lambda.ml], which is at the time of
   writing the limit for the size of sub-expressions that can be shared across
   switch branches. *)
(* 55 *)
Definition i32 : int := 32.
Extract Inlined Constant i32 => "32".
Definition max_hash_depth : int := i32.

(* 57-67 *)
(* PORT-GAP(loose): the optional parameter [?contents_hash] is by place, of
   type [option]; the function is not in the interface, and every call of
   the file gives it by place, so there is no wrapper with [?contents_hash]
   at the end of the extracted file. 64: the guard [when depth >=
   max_hash_depth] is an [if] in its case, and the case [_] is written in
   both places. *)
Definition create (contents_hash : option contents_hash_) (is_cold : bool)
    (expr : Expr.t) : M t :=
  (* Since we are building terms from the bottom-up, we don't know initially at
     which depth they will end up. Instead, we eagerly compute hashes as we
     rebuild expressions (so that computing the hash does not need another
     traversal), and zero it out when we reach the maximum depth. *)
  let* contents_hash :=
    match contents_hash with
    | Some {| depth := depth |} =>
      if depth >=? max_hash_depth
      then ret Or_null.null
      else Or_null.of_option contents_hash
    | None => Or_null.of_option contents_hash
    end
  in
  ret
    {| Rebuilt_expr.expr := expr;
       Rebuilt_expr.is_cold := is_cold;
       Rebuilt_expr.contents_hash := contents_hash
    |}.

(* 69 *)
Definition rebuilt_expr : Type := t.

(* 71-77 *)
Definition to_expr (t : Rebuilt_expr.t) (are_rebuilding : ART.t) : M Expr.t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then
    fatal_error
      "Cannot ask [Rebuilt_expr] for the built expression when [UA.do_not_rebuild_terms] is set"
  else ret t.(expr).

(* 79 *)
Definition descr (t : Rebuilt_expr.t) : M Flambda.expr_descr :=
  Expr.descr t.(expr).

(* 81-84 *)
Definition to_apply_cont (t : Rebuilt_expr.t) : M (option Apply_cont.t) :=
  let! tmp1 := descr t in
  match tmp1 with
  | Flambda.Apply_cont apply_cont => ret (Some apply_cont)
  | Flambda.Let _ | Flambda.Let_cont _ | Flambda.Apply _ | Flambda.Switch _
  | Flambda.Invalid _ =>
    ret None
  end.

(* 86-93 *)
Definition can_be_removed_as_invalid (t : Rebuilt_expr.t)
    (are_rebuilding : ART.t) : M bool :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret false
  else
    let! tmp2 := descr t in
    match tmp2 with
    | Flambda.Invalid _ =>
      let! tmp3 := Flambda_features.Debug.keep_invalid_handlers tt in
      if tmp3 then ret false else ret true
    | Flambda.Let _ | Flambda.Let_cont _ | Flambda.Apply _
    | Flambda.Apply_cont _ | Flambda.Switch _ =>
      ret false
    end.

(* 95-99 *)
(* PORT-GAP(loose): 95, the attribute [@ocamlformat "disable"] is not
   kept. *)
Definition print (are_rebuilding : ART.t) (ppf : Format.formatter)
    (t : Rebuilt_expr.t) : M unit :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then Format.fprintf0 ppf "<unavailable, terms not being rebuilt>"
  else Expr.print ppf t.(expr).

(* 101-102 *)
(* PORT-GAP(init): a value that the compiler computes with calls when the
   module starts: a parameter, realised by the compiler's text with the
   arguments of [create] by place. *)
Parameter term_not_rebuilt : t.
Extract Constant term_not_rebuilt =>
  "create None false (Expr.create_invalid Code_not_rebuilt)".

(* 104-115. [Simple.pattern_match' simple ~const ~symbol ~var]: the
   arguments are in the order of the interface, [var], [symbol], [const]. *)
Definition contents_hash_simple (simple : Simple.t) : M int :=
  (* We want a "structural" hash that doesn't depend on names bound by
     continuations, so we ignore the names of variables, including inside
     coercions (but we still record whether we had a coercion or not). *)
  Simple.pattern_match' simple
    (fun (_ : Variable_.t) coercion =>
      let* has_coercion :=
        let! tmp1 := Coercion.is_id coercion in
        ret (negb tmp1)
      in
      Hashtbl.hash (i2, has_coercion))
    (fun symbol coercion =>
      let* has_coercion :=
        let! tmp1 := Coercion.is_id coercion in
        ret (negb tmp1)
      in
      let! tmp1 := Symbol.hash symbol in
      Hashtbl.hash (T3 1 tmp1 has_coercion))
    (fun const =>
      let! tmp1 := Reg_width_const.hash const in
      Hashtbl.hash (0, tmp1)).

(* 117-151 *)
Definition create_let (are_rebuilding : ART.t) (bound_vars : Bound_pattern.t)
    (defining_expr : Named.t) (body : Rebuilt_expr.t)
    (free_names_of_body : Name_occurrences.t) : M Rebuilt_expr.t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret term_not_rebuilt
  else
    let* contents_hash :=
      match body.(Rebuilt_expr.contents_hash) with
      | Or_null.Null => ret None
      | Or_null.This {| depth := depth; structural_hash := body_hash |} =>
        (* PORT-GAP(loose): 126, the attribute [@local] is not kept. *)
        let& simple_expr :=
          fun (named_hash : int) =>
          let! tmp2 := Hashtbl.hash (T3 1 named_hash body_hash) in
          ret (Some {| depth := depth + 1; structural_hash := tmp2 |})
        in
        match defining_expr with
        | Flambda.Simple simple =>
          let! tmp2 := contents_hash_simple simple in
          let! tmp3 := Hashtbl.hash (0, tmp2) in
          simple_expr tmp3
        | Flambda.Prim prim _dbg =>
          let* args_hash :=
            let! tmp2 := Flambda_primitive.args prim in
            List.map contents_hash_simple tmp2
          in
          let* prim := Flambda_primitive.without_args prim in
          (* We use [Hashtbl.hash] directly on [prim] here, which should be
             fine. Worst case scenario, we have two primitives that should later
             compare equal but have different hashes (e.g. because they contain
             different regions), and we miss out on an optimisation. This should
             be rare and mostly inconsequential, though. *)
          let! tmp2 := Hashtbl.hash (T3 1 prim args_hash) in
          simple_expr tmp2
        | Flambda.Set_of_closures _ _ | Flambda.Static_consts _
        | Flambda.Rec_info _ =>
          ret None
        end
      end
    in
    (* 148-151: [a |> f |> g b] is [g b (f a)]. *)
    let! tmp2 :=
      Let.create bound_vars defining_expr body.(expr)
        (Or_unknown.Known free_names_of_body)
    in
    let! tmp3 := Expr.create_let tmp2 in
    create contents_hash body.(is_cold) tmp3.

(* 153-156 *)
Definition create_apply (are_rebuilding : ART.t) (is_cold : bool)
    (apply : Apply.t) : M t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret term_not_rebuilt
  else
    let! tmp2 := Expr.create_apply apply in
    create None is_cold tmp2.

(* 158-172 *)
Definition create_apply_cont (is_cold : bool) (apply_cont : Apply_cont.t)
    : M t :=
  let* contents_hash :=
    let! tmp1 := Apply_cont.trap_action apply_cont in
    match tmp1 with
    | Some _ => ret None
    | None =>
      let! tmp1 := Apply_cont.args apply_cont in
      let! tmp2 := List.map contents_hash_simple tmp1 in
      let! tmp3 := Apply_cont.continuation apply_cont in
      let! tmp4 := Continuation.hash tmp3 in
      let! tmp5 := Hashtbl.hash (T3 0 tmp4 tmp2) in
      ret (Some {| depth := 0; structural_hash := tmp5 |})
    end
  in
  let! tmp1 := Expr.create_apply_cont apply_cont in
  create contents_hash is_cold tmp1.

(* 174-191 *)
Module Function_params_and_body.
  (* 175 *)
  Definition t : Type := Flambda.Import_.Function_params_and_body.t.

  (* 177-181 *)
  Definition create (return_continuation exn_continuation : Continuation.t)
      (params : Bound_parameters.t) (body : rebuilt_expr)
      (free_names_of_body : Name_occurrences.t) (my_closure : Variable_.t)
      (my_alloc_mode : Alloc_mode.For_applications.t) (my_depth : Variable_.t)
      : M t :=
    Flambda.Import_.Function_params_and_body.create return_continuation
      exn_continuation params body.(expr)
      (Or_unknown.Known free_names_of_body)
      my_closure my_alloc_mode my_depth.

  (* 183-188 *)
  Definition to_function_params_and_body
      (t : Rebuilt_expr.Function_params_and_body.t) (are_rebuilding : ART.t)
      : M Flambda.Import_.Function_params_and_body.t :=
    let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
    if tmp1
    then
      fatal_error
        "Cannot ask for function params and body when not rebuilding terms"
    else ret t.

  (* 190 *)
  Definition is_my_closure_used (t : Rebuilt_expr.Function_params_and_body.t)
      : M bool :=
    Flambda.Import_.Function_params_and_body.is_my_closure_used t.
End Function_params_and_body.

(* 193-252 *)
Module Continuation_handler.
  (* 194-202 *)
  (* The type has an inline record. In Rocq it is the inductive type [t_],
     whose constructor takes the fields by place; the OCaml definition is the
     compiler's text, which the directive of [t] puts at this place of the
     extracted module. *)
  Inductive t_ : Type :=
  | Continuation_handler :
      Bound_parameters.t -> Flambda.expr -> Name_occurrences.t -> bool ->
      bool -> t_
  | Continuation_handler_not_rebuilt : t_.
  Extract Inductive t_ => "t"
    [ "(fun (x__1, x__2, x__3, x__4, x__5) -> Continuation_handler { params = x__1; handler = x__2; free_names_of_handler = x__3; is_exn_handler = x__4; is_cold = x__5 })"
      "Continuation_handler_not_rebuilt" ]
    "(fun f__1 f__2 x__0 -> match x__0 with Continuation_handler { params = x__1; handler = x__2; free_names_of_handler = x__3; is_exn_handler = x__4; is_cold = x__5 } -> f__1 x__1 x__2 x__3 x__4 x__5 | Continuation_handler_not_rebuilt -> f__2 ())".
  Definition t : Type := t_.
  Extract Constant t => "
    | Continuation_handler of
        { params : Bound_parameters.t;
          handler : Flambda.expr;
          free_names_of_handler : Name_occurrences.t;
          is_exn_handler : bool;
          is_cold : bool
        }
    | Continuation_handler_not_rebuilt
  ".

  (* 204-207 *)
  (* PORT-GAP(init): a value that the compiler computes with a call when
     the module starts: a parameter, realised by the compiler's text. *)
  Parameter dummy : Flambda.Import_.Continuation_handler.t.
  Extract Constant dummy => "
    Continuation_handler.create Bound_parameters.empty
      ~handler:term_not_rebuilt.expr ~free_names_of_handler:Unknown
      ~is_exn_handler:false ~is_cold:false".

  (* 209-234 *)
  Definition to_continuation_handler (body_is_cold : bool)
      (t : Rebuilt_expr.Continuation_handler.t)
      : M Flambda.Import_.Continuation_handler.t :=
    match t with
    | Continuation_handler_not_rebuilt => ret dummy
    | Continuation_handler params handler free_names_of_handler
        is_exn_handler is_cold =>
      (* If the body of the continuation handler is cold, then it is the
         responsibility of our context to introduce a coldness boundary (at
         another continuation handler or function definition).

         It is important that we clear the [is_cold] flag here: being cold
         prevents *all* inlining (both in flambda and cmm), but we only actually
         care about inlining of cold continuations into hot contexts (or across
         different cold contexts, e.g. within a loop and outside of a loop), not
         within a single cold context.

         Note that this is a (likely) good enough approximation but does not
         deal with all possible situations. For instance, if we have successive
         cold handlers ([let [@cold] k1 = ... in let[@cold] k2 = ... in ...])
         then we will still prevent inlining of [k1] into [k2]. This is likely
         fine, and not worth doing something specific to deal with that
         situation. Sinking the definition of [k1] to the dominator of its uses
         would cleanly prevent this issue. *)
      let& is_cold := is_cold && negb body_is_cold in
      Flambda.Import_.Continuation_handler.create params handler
        (Or_unknown.Known free_names_of_handler)
        is_exn_handler is_cold
    end.

  (* 236-238 *)
  Definition print (cont : Continuation.t) (recursive : Recursive.t)
      (ppf : Format.formatter) (ch : Rebuilt_expr.Continuation_handler.t)
      : M unit :=
    let! tmp1 := to_continuation_handler false ch in
    Flambda.Import_.Continuation_handler.print cont recursive ppf tmp1.

  (* 240-251 *)
  Definition create (are_rebuilding : ART.t) (params : Bound_parameters.t)
      (handler : rebuilt_expr) (free_names_of_handler : Name_occurrences.t)
      (is_exn_handler is_cold : bool) : M t :=
    let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
    if tmp1
    then ret Continuation_handler_not_rebuilt
    else
      ret
        (Continuation_handler params handler.(expr) free_names_of_handler
           is_exn_handler is_cold).
End Continuation_handler.

(* 254-265 *)
Definition create_non_recursive_let_cont (are_rebuilding : ART.t)
    (cont : Continuation.t) (handler : Continuation_handler.t)
    (body : Rebuilt_expr.t) (free_names_of_body : Name_occurrences.t)
    : M Rebuilt_expr.t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret term_not_rebuilt
  else
    let* handler :=
      Continuation_handler.to_continuation_handler body.(is_cold) handler
    in
    let! tmp2 :=
      Let_cont.create_non_recursive cont handler body.(expr)
        (Or_unknown.Known free_names_of_body)
    in
    create None body.(is_cold) tmp2.

(* 267-279 *)
Definition create_non_recursive_let_cont' (are_rebuilding : ART.t)
    (cont : Continuation.t) (handler : Continuation_handler.t)
    (body : Rebuilt_expr.t)
    (num_free_occurrences_of_cont_in_body : Num_occurrences.t)
    (is_applied_with_traps : bool) : M Rebuilt_expr.t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret term_not_rebuilt
  else
    let* handler :=
      Continuation_handler.to_continuation_handler body.(is_cold) handler
    in
    let! tmp2 :=
      Let_cont.create_non_recursive' cont handler body.(expr)
        (Or_unknown.Known num_free_occurrences_of_cont_in_body)
        is_applied_with_traps
    in
    create None body.(is_cold) tmp2.

(* 281-292 *)
Definition create_non_recursive_let_cont_without_free_names
    (are_rebuilding : ART.t) (cont : Continuation.t)
    (handler : Continuation_handler.t) (body : Rebuilt_expr.t)
    : M Rebuilt_expr.t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret term_not_rebuilt
  else
    let* handler :=
      Continuation_handler.to_continuation_handler body.(is_cold) handler
    in
    let! tmp2 :=
      Let_cont.create_non_recursive cont handler body.(expr)
        Or_unknown.Unknown
    in
    create None body.(is_cold) tmp2.

(* 294-304 *)
Definition create_recursive_let_cont (are_rebuilding : ART.t)
    (invariant_params : Bound_parameters.t)
    (handlers : Continuation.Lmap.t Continuation_handler.t)
    (body : Rebuilt_expr.t) : M Rebuilt_expr.t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret term_not_rebuilt
  else
    (* 299-301: the function of the file is given its first argument only: a
       value. *)
    let* handlers :=
      Continuation.Lmap.map
        (Continuation_handler.to_continuation_handler body.(is_cold))
        handlers
    in
    let! tmp2 :=
      Let_cont.create_recursive invariant_params handlers body.(expr)
    in
    create None body.(is_cold) tmp2.

(* 306-309 *)
Definition create_switch (are_rebuilding : ART.t) (is_cold : bool)
    (switch : Switch_expr.t) : M t :=
  let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
  if tmp1
  then ret term_not_rebuilt
  else
    let! tmp2 := Expr.create_switch switch in
    create None is_cold tmp2.

(* 311 *)
Definition create_invalid (reason : Flambda.Invalid.t) : M t :=
  let! tmp1 := Expr.create_invalid reason in
  create None true tmp1.

(* 313-340. [ListLabels.fold_left (List.rev bindings) ~init ~f]: the
   arguments are in the order of the interface. The two triples that the
   function [~f] takes apart are named [acc] and [binding]: names that the
   compiler does not have. *)
Definition bind_no_simplification (are_rebuilding : ART.t)
    (bindings : list (tuple3 Bound_var.t Code_size.t Named.t))
    (body : Rebuilt_expr.t) (cost_metrics_of_body : Cost_metrics.t)
    (free_names_of_body : Name_occurrences.t)
    : M (tuple3 Rebuilt_expr.t Cost_metrics.t Name_occurrences.t) :=
  let! tmp1 := List.rev bindings in
  ListLabels.fold_left
    (fun acc binding =>
      let* '(T3 expr cost_metrics free_names) := ret acc in
      let* '(T3 var size_of_defining_expr defining_expr) := ret binding in
      let* expr :=
        let! tmp2 := Bound_pattern.singleton var in
        create_let are_rebuilding tmp2 defining_expr expr free_names
      in
      let* free_names :=
        let! tmp2 := Bound_var.var var in
        let! tmp3 := Name_occurrences.remove_var free_names tmp2 in
        let! tmp4 := Named.free_names defining_expr in
        Name_occurrences.union tmp4 tmp3
      in
      let* is_phantom :=
        let! tmp2 := Bound_var.name_mode var in
        Name_mode.is_phantom tmp2
      in
      let* cost_metrics_of_defining_expr :=
        Cost_metrics.from_size size_of_defining_expr
      in
      let* cost_metrics :=
        let! tmp2 :=
          Cost_metrics.increase_due_to_let_expr is_phantom
            cost_metrics_of_defining_expr
        in
        Cost_metrics.op_plus cost_metrics tmp2
      in
      ret (T3 expr cost_metrics free_names))
    (T3 body cost_metrics_of_body free_names_of_body)
    tmp1.

(* 342-663 *)
Module Matching_for_unique_handler.
  (* Computes an approximate equality between terms. Terms that are equal in
     this way can be substituted for each other, and in particular two
     continuation handlers with equal content can be merged.

     As an extension, we support detecting continuations that have identical
     handlers up to permutation of their parameters.

     This is done by a matching algorithm that enforce a bipartite matching
     between the parameters of the two continuations when they occur at the same
     position in the term. *)

  (* 354: [exception Match_failure] is at the head of the extracted file. *)
  Parameter Match_failure : exception unit.
  Extract Inlined Constant Match_failure =>
    "((fun () -> Match_failure), (function Match_failure -> Some () | _ -> None))".

  (* 356 *)
  Definition fail {A : Type} (_ : unit) : M A := raise_ Match_failure tt.

  (* 358 *)
  Definition fail_if_not (b : bool) : M unit :=
    if negb b then raise_ Match_failure tt else ret tt.

  (* 360 *)
  Definition fail_if_not_equal {X Y : Type} (f : X -> Y -> M bool) (x : X)
      (y : Y) : M unit :=
    let! tmp1 := f x y in
    fail_if_not tmp1.

  (* 362-457 *)
  (* PORT-GAP(loose): 362-389, the signature of the module is not kept: its
     type [t] is not abstract and what is before it in the module is seen
     from outside. *)
  Module Match_permutable_parameters.
    (* 363-366, the comment of the type [t] in the signature: *)
    (** Bipartite matcher between two lists of parameters.

        This is an imperative data structure that gets updated by calling
        [match_variable]. *)

    (* 390: [module HV = Hashtbl.Make (Variable)] is at the head of the
       extracted file. *)

    (* 392-397 *)
    (** Represents a parameter in one of the two parameter lists, and maps it to
        the corresponding parameter (as a variable) in the other list. *)
    (* PORT-GAP(type): the record has a mutable field. In Rocq the type is
       abstract: [mk_parameter_on_one_side] makes a record (in the monad:
       the record has a state), [kind] reads the field that does not
       change, [get_matching_variable_on_other_side] and
       [set_matching_variable_on_other_side] read and set the mutable field
       (in the monad). The OCaml definition is the compiler's text; the
       four functions are realised by OCaml texts written for this file,
       and Rocq prints them here as four definitions that the compiler does
       not have. *)
    Parameter parameter_on_one_side : Type.
    Extract Constant parameter_on_one_side =>
      "{ kind : Flambda_kind.With_subkind.t; mutable matching_variable_on_other_side : Variable.t option }".
    Parameter mk_parameter_on_one_side :
      Flambda_kind.With_subkind.t -> option Variable_.t ->
      M parameter_on_one_side.
    Extract Constant mk_parameter_on_one_side =>
      "fun kind matching_variable_on_other_side -> { kind; matching_variable_on_other_side }".
    Parameter kind : parameter_on_one_side -> Flambda_kind.With_subkind.t.
    Extract Constant kind => "fun p -> p.kind".
    Parameter get_matching_variable_on_other_side :
      parameter_on_one_side -> M (option Variable_.t).
    Extract Constant get_matching_variable_on_other_side =>
      "fun p -> p.matching_variable_on_other_side".
    Parameter set_matching_variable_on_other_side :
      parameter_on_one_side -> option Variable_.t -> M unit.
    Extract Constant set_matching_variable_on_other_side =>
      "fun p v -> p.matching_variable_on_other_side <- v".

    (* PORT-GAP(decl): what the file uses of [HV], declared here and not
       taken from decl/Rebuilt_expr__local.v: there the type [HV.t] has a
       parameter, so Rocq would print it under the path of that file and
       write [open Rebuilt_expr__local], which OCaml does not have. Here
       the type of the tables of this file has no parameter. *)
    Parameter HV_t : Type.
    Extract Inlined Constant HV_t => "parameter_on_one_side HV.t".
    Parameter HV_create : int -> M HV_t.
    Extract Inlined Constant HV_create => "HV.create".
    Parameter HV_find : HV_t -> Variable_.t -> M parameter_on_one_side.
    Extract Inlined Constant HV_find => "HV.find".
    Parameter HV_replace :
      HV_t -> Variable_.t -> parameter_on_one_side -> M unit.
    Extract Inlined Constant HV_replace => "HV.replace".

    (* 399-406 *)
    Record t : Type :=
      { params1 : HV_t;
            (* Keys are parameters from the first side (identified by their
               variable). *)
        params2 : HV_t
            (* Keys are parameters from the second side (identified by their
               variable). *)
      }.

    (* 408-414. 383-386, the comment of the function in the signature: *)
    (** Returns an argument that can be used to bind the provided parameter from
        the second list from a parameter in the first list.

        Fails if the parameter has not been matched. *)
    Definition matching_variable_for_param2
        (t : Match_permutable_parameters.t) (param2 : Bound_parameter.t)
        : M Variable_.t :=
      match_exn
        (fun _ =>
          let! tmp1 := Bound_parameter.var param2 in
          HV_find t.(params2) tmp1)
        Not_found
        (fun _ =>
          fatal_errorf2 "Parameter %a is not bound on the second side"
            Bound_parameter.print param2)
        (fun binding =>
          (* 413-414: the record patterns [{ matching_variable_on_other_side
             = None; _ }] and [... = Some var; _ }] are the reading of the
             mutable field, then a match. *)
          let! tmp1 := get_matching_variable_on_other_side binding in
          match tmp1 with
          | None => fail tt
          | Some var => ret var
          end).

    (* 416-432. 369-371, the comment of the function in the signature: *)
    (** Create a new matcher.

        Fails if the two parameter lists have distinct number of parameters. *)
    Definition create (params1 params2 : Bound_parameters.t) : M t :=
      (* Must have the same number of parameters in both cases, but we allow
         permutations -- kinds are checked in [match_variable]. *)
      (let! tmp1 := Bound_parameters.same_number params1 params2 in
       if negb tmp1 then fail tt else ret tt) ;;
      let& create_mapping :=
        fun (params : Bound_parameters.t) =>
        let* table := HV_create i16 in
        (let! tmp4 := Bound_parameters.to_list params in
         List.iter
           (fun param =>
             let! tmp1 := Bound_parameter.kind param in
             let! tmp2 := mk_parameter_on_one_side tmp1 None in
             let! tmp3 := Bound_parameter.var param in
             HV_replace table tmp3 tmp2)
           tmp4) ;;
        ret table
      in
      (* PORT-GAP(record-order): 432, calls in the two fields: the last
         field first, each bound by [let*] ([mapping2], [mapping1]: names
         that the compiler does not have).
         VERDICT (record_order/README.md, place 11): COMMUTE. Each call of
         [create_mapping] fills a table that it has just made: two
         allocations. *)
      let* mapping2 := create_mapping params2 in
      let* mapping1 := create_mapping params1 in
      ret
        {| Match_permutable_parameters.params1 := mapping1;
           Match_permutable_parameters.params2 := mapping2
        |}.

    (* 434-456. 374-380, the comment of the function in the signature: *)
    (** [match_variable t var1 var2] records that [var1] and [var2] must match
        in the respective parameter lists.

        Fails if either [var1] or [var2] are not part of this matching, if
        either has already been matched to another variable, or if [var1] and
        [var2] are bound with incompatible kinds in their respective parameter
        lists. *)
    Definition match_variable (t : Match_permutable_parameters.t)
        (var1 var2 : Variable_.t) : M unit :=
      match_exn
        (fun _ => HV_find t.(params1) var1)
        Not_found
        (fun _ => (* [var1] is not a parameter for this permutation *) fail tt)
        (fun binding1 =>
          let! tmp1 := get_matching_variable_on_other_side binding1 in
          match tmp1 with
          | Some var2' =>
            (* [var1] is a parameter and is already matched *)
            fail_if_not_equal Variable_.equal var2' var2
          | None =>
            (* [var1] is a parameter, but not yet matched: try to match
               it. *)
            let& kind1 := kind binding1 in
            match_exn
              (fun _ => HV_find t.(params2) var2)
              Not_found
              (fun _ =>
                (* [var2] is either not a parameter of the same
                   continuation, or already matched to another parameter in
                   the first list. *)
                fail tt)
              (fun binding2 =>
                let! tmp1 := get_matching_variable_on_other_side binding2 in
                match tmp1 with
                | Some _ => fail tt
                | None =>
                  (* [var2] is a parameter of the same continuation and is
                     not yet matched: we can match [var1] and [var2] if the
                     kinds agree. *)
                  let& kind2 := kind binding2 in
                  fail_if_not_equal Flambda_kind.With_subkind.equal kind1
                    kind2 ;;
                  set_matching_variable_on_other_side binding1 (Some var2) ;;
                  set_matching_variable_on_other_side binding2 (Some var1)
                end)
          end).
  End Match_permutable_parameters.

  (* 459-486 *)
  (** Maps each variable that is a parameter to the corresponding matching
      between two [Bound_parameters.t].

      It might be surprising to see two nested mappings from variables here,
      since [Match_permutable_parameters] is itself a mapping from variables.
      The two nested mappings have fundamentally distinct meanings: the outer
      mapping ([matching_env]) maps variables to the permutation (if any) that
      they participate in, while the inner mapping
      ([Match_permutable_parameters]) records, for each variable participating
      in that specific permutation, its matching parameter in the other list.

      This is helpful in two situations:

      - For exception handlers, the exception parameter is matched directly and
        then there is a permutation for the remaining params.

      - If we want to support deduplication of continuations containing
        [let_cont]s, we must make sure not to match variables from different
        continuations together, which is taken care of by creating a distinct
        [Match_permutable_parameters] instance for each continuation.

      {b Note}: Matching information is recorded by mutably modifying the
      [Match_permutable_parameters.t] instance(s), so environments should only
      be passed down the call stack, not returned. *)
  Record matching_env : Type :=
    { permutable_params1 : Variable_.Map.t Match_permutable_parameters.t;
      permutable_params2 : Variable_.Map.t Match_permutable_parameters.t
    }.

  (* 488-496 *)
  Definition match_variable (env : matching_env) (var1 var2 : Variable_.t)
      : M unit :=
    let! tmp1 := Variable_.Map.find_or_null var1 env.(permutable_params1) in
    match tmp1 with
    | Or_null.Null =>
      (* [var1] is not a parameter: both variables must be equal, and [var2]
         must not be a parameter either. *)
      (let! tmp1 := Variable_.Map.mem var2 env.(permutable_params2) in
       if tmp1 then fail tt else ret tt) ;;
      fail_if_not_equal Variable_.equal var1 var2
    | Or_null.This permutation =>
      Match_permutable_parameters.match_variable permutation var1 var2
    end.

  (* 506-511 *)
  (* PORT-GAP(loose): 498-504, the module type [Equal_and_free_names] is not
     kept, and 506-507, the first-class module [(module T :
     Equal_and_free_names with type t = t)] is its two functions [equal] and
     [free_names], by place: the function has one argument more. *)
  Definition match_equal_and_free_names {T : Type} (equal : T -> T -> M bool)
      (free_names : T -> M Name_occurrences.t) (env : matching_env)
      (t1 t2 : T) : M unit :=
    (* Make sure that the variables contained within are equal on both
       sides. *)
    fail_if_not_equal equal t1 t2 ;;
    let! tmp1 := free_names t1 in
    Name_occurrences.fold_variables tmp1 tt
      (fun (_ : unit) var => match_variable env var var).

  (* 513-520 *)
  Definition match_name (env : matching_env) (name1 name2 : Name.t)
      : M unit :=
    Name.pattern_match name1
      (fun var1 =>
        Name.pattern_match name2
          (fun var2 => match_variable env var1 var2)
          (fun _ => fail tt))
      (fun symbol1 =>
        let! tmp1 := Name.symbol symbol1 in
        fail_if_not_equal Name.equal name2 tmp1).

  (* 522-534. [Simple.pattern_match simple ~const ~name]: the arguments are
     in the order of the interface, [name] then [const]. *)
  Definition match_simple (env : matching_env) (simple1 simple2 : Simple.t)
      : M unit :=
    Simple.pattern_match simple1
      (fun name1 coercion1 =>
        Simple.pattern_match simple2
          (fun name2 coercion2 =>
            (* 533: [(module Coercion)] *)
            match_equal_and_free_names Coercion.equal Coercion.free_names env
              coercion1 coercion2 ;;
            match_name env name1 name2)
          (fun _ => fail tt))
      (fun const1 =>
        Simple.pattern_match simple2
          (fun _ _ => fail tt)
          (fun const2 =>
            fail_if_not_equal Reg_width_const.equal const1 const2)).

  (* 536-543. Like [iter2], but raises [Match_failure] if the lengths are
     not equal *)
  Fixpoint match_list {Env X Y : Type} (match_elt : Env -> X -> Y -> M unit)
      (env : Env) (xs : list X) (ys : list Y) {struct xs} : M unit :=
    match xs, ys with
    | [], [] => ret tt
    | [], _ | _, [] => fail tt
    | x :: xs, y :: ys =>
      match_elt env x y ;;
      match_list match_elt env xs ys
    end.

  (* 545-546 *)
  Definition match_simples (env : matching_env)
      (simples1 simples2 : list Simple.t) : M unit :=
    match_list match_simple env simples1 simples2.

  (* 548-553 *)
  Definition match_primitive (env : matching_env)
      (prim1 prim2 : Flambda_primitive.t) : M unit :=
    (* PORT-GAP(loose): 549, [let module P = Flambda_primitive in] is not
       kept: the module is written by its name. 551: [(module
       P.Without_args)]. *)
    (let! tmp1 := Flambda_primitive.without_args prim2 in
     let! tmp2 := Flambda_primitive.without_args prim1 in
     match_equal_and_free_names Flambda_primitive.Without_args.equal
       Flambda_primitive.Without_args.free_names env tmp2 tmp1) ;;
    let! tmp1 := Flambda_primitive.args prim2 in
    let! tmp2 := Flambda_primitive.args prim1 in
    match_simples env tmp2 tmp1.

  (* 555-569 *)
  Definition match_named (env : matching_env) (named1 named2 : Named.t)
      : M unit :=
    (* We only try to match simples and prims; other types of [named]s prevent
       deduplication.

       It is unlikely we find the same set of closure twice since we resimplify
       them; static consts are already deduplicated separately, and rec infos
       are unlikely to appear in the continuations we want to deduplicate (arms
       of switches). *)
    match named1, named2 with
    | Flambda.Simple simple1, Flambda.Simple simple2 =>
      match_simple env simple1 simple2
    | Flambda.Prim prim1 _dbg1, Flambda.Prim prim2 _dbg2 =>
      match_primitive env prim1 prim2
    | ( Flambda.Simple _ | Flambda.Prim _ _ | Flambda.Set_of_closures _ _
      | Flambda.Static_consts _ | Flambda.Rec_info _ ), _ =>
      fail tt
    end.

  (* 571-612. In the matches on two calls, each call is bound by [let*], the
     second one first ([descr2], [descr1], [trap_action2], [trap_action1]:
     names that the compiler does not have). *)
  Fixpoint match_expr (fuel : fuel) (env : matching_env) (t1 t2 : Expr.t)
      {struct fuel} : M unit :=
    recursive! fuel in
    let* descr2 := Expr.descr t2 in
    let* descr1 := Expr.descr t1 in
    match descr1, descr2 with
    | Flambda.Let let_expr1, Flambda.Let let_expr2 =>
      match_let_expr fuel env let_expr1 let_expr2
    | Flambda.Apply_cont apply_cont1, Flambda.Apply_cont apply_cont2 =>
      match_apply_cont fuel env apply_cont1 apply_cont2
    | ( Flambda.Let _ | Flambda.Let_cont _ | Flambda.Apply _
      | Flambda.Apply_cont _ | Flambda.Switch _ | Flambda.Invalid _ ), _ =>
      fail tt
    end

  (* 583-597 *)
  with match_let_expr (fuel : fuel) (env : matching_env)
      (let_expr1 let_expr2 : Let.t) {struct fuel} : M unit :=
    recursive! fuel in
    (* This call to [match_named] ensures that the kinds for the bound
       patterns below match. *)
    (let! tmp1 := Let.defining_expr let_expr2 in
     let! tmp2 := Let.defining_expr let_expr1 in
     match_named env tmp2 tmp1) ;;
    Let.pattern_match let_expr1
      (fun bound_pattern1 body1 =>
        Let.pattern_match let_expr2
          (fun bound_pattern2 body2 =>
            match bound_pattern1, bound_pattern2 with
            | Bound_pattern.Singleton bound_var1,
              Bound_pattern.Singleton bound_var2 =>
              let* body2 :=
                let! tmp1 := Bound_var.var bound_var1 in
                let! tmp2 := Bound_var.var bound_var2 in
                let! tmp3 := Renaming.add_variable Renaming.empty tmp2 tmp1 in
                Expr.apply_renaming body2 tmp3
              in
              match_expr fuel env body1 body2
            | ( Bound_pattern.Singleton _ | Bound_pattern.Set_of_closures _
              | Bound_pattern.Static _ ), _ =>
              fail tt
            end))

  (* 599-612 *)
  with match_apply_cont (fuel : fuel) (env : matching_env)
      (apply_cont1 apply_cont2 : Apply_cont.t) {struct fuel} : M unit :=
    recursive! fuel in
    let* trap_action2 := Apply_cont.trap_action apply_cont2 in
    let* trap_action1 := Apply_cont.trap_action apply_cont1 in
    match trap_action1, trap_action2 with
    | None, None =>
      (let! tmp1 := Apply_cont.continuation apply_cont2 in
       let! tmp2 := Apply_cont.continuation apply_cont1 in
       fail_if_not_equal Continuation.equal tmp2 tmp1) ;;
      let! tmp1 := Apply_cont.args apply_cont2 in
      let! tmp2 := Apply_cont.args apply_cont1 in
      match_simples env tmp2 tmp1
    | _, _ => fail tt
    end.

  (* 614-635 *)
  Definition match_permutable_continuation_handler
      (params1 : Bound_parameters.t) (handler1 : Expr.t)
      (params2 : Bound_parameters.t) (handler2 : Expr.t)
      : M (list Simple.t) :=
    let* permutation := Match_permutable_parameters.create params1 params2 in
    let& create_permutable_params :=
      fun (params : Bound_parameters.t) =>
      let! tmp1 := Bound_parameters.to_list params in
      List.fold_left
        (fun env param =>
          let! tmp2 := Bound_parameter.var param in
          Variable_.Map.add tmp2 permutation env)
        Variable_.Map.empty tmp1
    in
    let* permutable_params1 := create_permutable_params params1 in
    let* permutable_params2 := create_permutable_params params2 in
    (let_fuel! fuel in
     match_expr fuel
       {| Matching_for_unique_handler.permutable_params1 := permutable_params1;
          Matching_for_unique_handler.permutable_params2 := permutable_params2
       |}
       handler1 handler2) ;;
    (* We are matching continuation handlers after rebuilding/dataflow, so we
       expect that all parameters are used and we can reconstruct a suitable
       bijection, so if we get there, this should never raise (but it is also
       harmless if it does). *)
    let! tmp1 := Bound_parameters.to_list params2 in
    List.map
      (fun param2 =>
        let! tmp2 :=
          Match_permutable_parameters.matching_variable_for_param2 permutation
            param2
        in
        Simple.var tmp2)
      tmp1.

  (* 637-662 *)
  Definition match_non_recursive_continuation_handler (is_exn_handler : bool)
      (params1 : Bound_parameters.t) (handler1 : Expr.t)
      (params2 : Bound_parameters.t) (handler2 : Expr.t)
      : M (list Simple.t) :=
    if is_exn_handler
    then
      (* If we are trying to share exception handlers, their first
         (exception) argument must match. 643-645: each of the two calls
         that are matched is bound by [let*], the second one first
         ([list2], [list1]: names that the compiler does not have). *)
      let* list2 := Bound_parameters.to_list params2 in
      let* list1 := Bound_parameters.to_list params1 in
      match list1, list2 with
      | [], _ | _, [] => fail tt
      | exn1 :: params1, exn2 :: params2 =>
        (let! tmp1 := Bound_parameter.kind exn2 in
         let! tmp2 := Bound_parameter.kind exn1 in
         fail_if_not_equal Flambda_kind.With_subkind.equal tmp2 tmp1) ;;
        let* handler2 :=
          let! tmp1 := Bound_parameter.var exn1 in
          let! tmp2 := Bound_parameter.var exn2 in
          let! tmp3 := Renaming.add_variable Renaming.empty tmp2 tmp1 in
          Expr.apply_renaming handler2 tmp3
        in
        let! tmp1 := Bound_parameters.create params2 in
        let! tmp2 := Bound_parameters.create params1 in
        let! tmp3 :=
          match_permutable_continuation_handler tmp2 handler1 tmp1 handler2
        in
        let! tmp4 := Bound_parameter.simple exn1 in
        ret (tmp4 :: tmp3)
      end
    else
      match_permutable_continuation_handler params1 handler1 params2 handler2.
End Matching_for_unique_handler.

(* 665-673 *)
Definition match_continuation_handler (is_exn_handler : bool)
    (params1 : Bound_parameters.t) (handler1 : Expr.t)
    (params2 : Bound_parameters.t) (handler2 : Expr.t)
    : M (option (list Simple.t)) :=
  (* PORT-GAP(loose): 667, [let open Matching_for_unique_handler in] is not
     kept: the names of the module are written with its name. *)
  match_exn
    (fun _ =>
      Matching_for_unique_handler.match_non_recursive_continuation_handler
        is_exn_handler params1 handler1 params2 handler2)
    Matching_for_unique_handler.Match_failure
    (fun _ => ret None)
    (fun args => ret (Some args)).

(* 675-753 *)
Module Unique_continuation_handlers.
  (* 676-681 *)
  Record entry (A : Type) : Type :=
    { params : Bound_parameters.t;
      handler : Expr.t;
      is_exn_handler : bool;
      payload : A
    }.
  Arguments params {A}.
  Arguments handler {A}.
  Arguments is_exn_handler {A}.
  Arguments payload {A}.

  (* 683 *)
  (* PORT-GAP(loose): 683, the attribute [@@unboxed] is not kept. *)
  Record t (A : Type) : Type :=
    { hash_map : Numeric_types.Int.Map.t (list (entry A)) }.
  Arguments hash_map {A}.

  (* 685 *)
  Definition empty {A : Type} : t A :=
    {| hash_map := Numeric_types.Int.Map.empty |}.

  (* 687-708 *)
  Definition contents_hash (are_rebuilding : ART.t) (handler : rebuilt_expr)
      (is_exn_handler : bool) (free_names_without_params : Name_occurrences.t)
      : M (Or_null.t int) :=
    let! tmp1 := ART.do_not_rebuild_terms are_rebuilding in
    if tmp1
    then ret Or_null.null
    else
      match handler.(Rebuilt_expr.contents_hash) with
      | Or_null.Null => ret Or_null.null
      | Or_null.This
          {| depth := depth; structural_hash := structural_hash |} =>
        (* The [contents_hash] does not include variable names (it is not clear
           how to do this up to alpha-equivalence since we are computing the
           hashes from the bottom up), so we include the free names of variables
           in the hash.

           This is an approximation, since we can't distinguish e.g. [x + y]
           from [y + x] in this way, but should be discriminating enough.

           CR-someday bclement: consider occurrence count. *)
        let! tmp1 := Bool.hash is_exn_handler in
        let! tmp2 := Hashtbl.hash (T3 depth structural_hash tmp1) in
        let! tmp3 :=
          Name_occurrences.fold_variables free_names_without_params tmp2
            (fun hash var =>
              let! tmp4 := Variable_.hash var in
              Hashtbl.hash (hash, tmp4))
        in
        Or_null.this tmp3
      end.

  (* 710-727 *)
  Definition add {A : Type} (are_rebuilding : ART.t)
      (params : Bound_parameters.t) (handler : rebuilt_expr)
      (is_exn_handler : bool) (free_names_without_params : Name_occurrences.t)
      (value : A) (t : Unique_continuation_handlers.t A)
      : M (Unique_continuation_handlers.t A) :=
    let! tmp1 :=
      contents_hash are_rebuilding handler is_exn_handler
        free_names_without_params
    in
    match tmp1 with
    | Or_null.Null => ret t
    | Or_null.This hash =>
      let* entries :=
        let! tmp1 := Numeric_types.Int.Map.find_or_null hash t.(hash_map) in
        match tmp1 with
        | Or_null.Null => ret []
        | Or_null.This entries => ret entries
        end
      in
      let& entry :=
        {| Unique_continuation_handlers.params := params;
           Unique_continuation_handlers.handler := handler.(expr);
           Unique_continuation_handlers.is_exn_handler := is_exn_handler;
           payload := value
        |}
      in
      let! tmp1 :=
        Numeric_types.Int.Map.add hash (entry :: entries) t.(hash_map)
      in
      ret {| hash_map := tmp1 |}
    end.

  (* 729-752 *)
  Definition find_opt {A : Type} (are_rebuilding : ART.t)
      (params : Bound_parameters.t) (handler : rebuilt_expr)
      (is_exn_handler : bool) (free_names_without_params : Name_occurrences.t)
      (t : Unique_continuation_handlers.t A) : M (option (A * list Simple.t)) :=
    let! tmp1 :=
      contents_hash are_rebuilding handler is_exn_handler
        free_names_without_params
    in
    match tmp1 with
    | Or_null.Null => ret None
    | Or_null.This hash =>
      (* 737-752: [List.find_map f |> Option.bind o] is [Option.bind o
         (List.find_map f)]. *)
      let! tmp3 :=
        papp1 List.find_map
          (fun (entry : Unique_continuation_handlers.entry A) =>
            let 'Build_entry _ other_params other_handler other_is_exn_handler
                   value := entry in
            let! tmp1 := Bool.equal is_exn_handler other_is_exn_handler in
            if tmp1
            then
              let! tmp2 :=
                match_continuation_handler is_exn_handler params
                  handler.(expr) other_params other_handler
              in
              Option.map (fun args => ret (value, args)) tmp2
            else ret None)
      in
      let! tmp4 := Numeric_types.Int.Map.find_opt hash t.(hash_map) in
      Option.bind tmp4 tmp3
    end.
End Unique_continuation_handlers.
