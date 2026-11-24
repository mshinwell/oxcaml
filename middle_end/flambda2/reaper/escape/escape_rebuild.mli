(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2026 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** The rebuilding side of the escape analysis (see [Escape_analysis]): turning
    the allocations it found to be local into stack allocations, inserting the
    regions they live in, and changing the calling convention of the functions
    made to return at mode local. These functions are called from [Rebuild].

    When the analysis has not been run (see [create]), all of them leave the
    terms, modes and metadata they are given unchanged. *)

type t

(** The state for rebuilding a compilation unit. The analysis has been run if
    the graph has been solved (see [Escape_graph.solved]).

    - [is_unboxed] tells which allocations the reaper unboxes, and
      [allocation_is_kept] which variables bound to allocations it keeps (the
      latter is only used for the statistics);
    - [code_ids_directly_called] is [Analysis.code_id_actually_directly_called];
    - [get_code_metadata] gives the metadata of any code (only used for the
      statistics). *)
val create :
  Escape_graph.t ->
  is_unboxed:(Code_id_or_name.t -> bool) ->
  allocation_is_kept:(Variable.t -> bool) ->
  code_ids_directly_called:(Name.t -> Code_id.Set.t Or_unknown.t) ->
  get_code_metadata:(Code_id.t -> Code_metadata.t) ->
  continuation_info:Traverse_acc.Continuation_info.t Continuation.Map.t ->
  machine_width:Target_system.Machine_width.t ->
  t

(** Print the statistics on the heap allocations seen by [localize] (blocks,
    boxed numbers and sets of closures): how many were made local and how many
    stayed on the heap, with their sizes in words. Nothing is printed unless the
    reaper debug flag [escape-stats] (one line per compilation unit) or
    [escape-stats-verbose] (also one line per allocation) is given; see
    [escape_rebuild.ml] for the format. *)
val report_stats : t -> unit

(** The defining expression of a [Let], to be rebuilt in place of the given one:
    a heap allocation (of a block, boxed number or set of closures) that the
    analysis decided to make local allocates in the innermost region. *)
val localize : t -> Bound_pattern.t -> Rev_expr.rev_named -> Rev_expr.rev_named

(** See [Escape_solution.adjust_code_metadata]. *)
val adjust_code_metadata : t -> Code_id.t -> Code_metadata.t -> Code_metadata.t

(** Close the regions left by a jump to the given continuation, before the given
    expression (which performs the jump). *)
val end_regions_before_jump :
  t -> Continuation.t -> Rebuilt_expr.t -> Rebuilt_expr.t

(** Redirect the arms of a [Switch] jumping to continuations that leave regions
    through continuations closing these regions. [params_of_continuation] must
    give fresh parameters for the continuation, as it is rebuilt. *)
val redirect_switch_arms :
  t ->
  params_of_continuation:(Continuation.t -> Bound_parameter.t list) ->
  Switch_arm.t Target_ocaml_int.Map.t ->
  Switch_arm.t Target_ocaml_int.Map.t

(** Rebuild an application with [rebuild], after giving it a local return mode
    if the callee was made to return at mode local, and close the regions left
    when it returns. *)
val rebuild_apply :
  t ->
  params_of_continuation:(Continuation.t -> Bound_parameter.t list) ->
  Flambda.Apply.t ->
  rebuild:(Flambda.Apply.t -> Rebuilt_expr.t) ->
  Rebuilt_expr.t

(** Rebuild the handler of the given recursive continuation, adding a region
    around it if needed (see [Escape_graph.recursive_scope]). *)
val rebuild_recursive_handler :
  t ->
  Continuation.t ->
  rebuild_body:(t -> Rebuilt_expr.t * 'r) ->
  Rebuilt_expr.t * 'r

(** Enter the body of a function: returns its allocation mode, made
    [Maybe_alloc_stack] if the function is to return at mode local. *)
val enter_function :
  t ->
  code_id:Code_id.t ->
  return_continuation:Continuation.t ->
  my_alloc_mode:Alloc_mode.For_applications.t ->
  Alloc_mode.For_applications.t * t

(** Rebuild the body of a function (entered with [enter_function]), adding a
    region around it if needed. *)
val rebuild_function_body :
  t ->
  code_id:Code_id.t ->
  rebuild_body:(t -> Rebuilt_expr.t * 'r) ->
  Rebuilt_expr.t * 'r
