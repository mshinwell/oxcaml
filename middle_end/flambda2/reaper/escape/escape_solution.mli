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

(** The decisions of the escape analysis (see [Escape_analysis]) needed for
    rebuilding, extracted from the solved Datalog database. *)

type t

(** [is_unboxed] tells which allocations the unboxing analysis is going to
    remove (see [Unboxing_analysis.result]). *)
val create : Datalog.database -> is_unboxed:(Code_id_or_name.t -> bool) -> t

(** Whether the allocation bound to the given variable was a candidate for stack
    allocation (see [Escape_graph.Relations.allocated_in]). *)
val is_candidate : t -> Variable.t -> bool

(** Whether the allocation bound to the given variable may be turned into a
    stack allocation. *)
val is_local_allocation : t -> Variable.t -> bool

(** Whether the given region scope (the code id of a function, or the dummy
    variable of a recursive [Let_cont], see [Escape_env.region_scope]) contains
    at least one allocation for which [is_local_allocation] holds and which will
    not be unboxed, or a call to a function returning at mode local, so that a
    region must be introduced. *)
val scope_needs_region : t -> Code_id_or_name.t -> bool

(** Whether the function is to allocate its result in its caller's region (see
    [Escape_analysis.local_return_tbl]). *)
val returns_local : t -> Code_id.t -> bool

(** Adjust the metadata of a function according to the decisions of the
    analysis: a function made to return at mode local gets a [result_mode] of
    kind [Maybe_alloc_stack] (its call sites get a [return_mode] of that kind,
    see [Escape_rebuild]) and [nlocal >= 1] (see [First_complex_local_param]),
    and the code of a local closure gets [nlocal] equal to its arity. *)
val adjust_code_metadata : t -> Code_id.t -> Code_metadata.t -> Code_metadata.t
