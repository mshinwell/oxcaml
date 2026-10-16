(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Nathanaelle Courant, Pierre Chambart, OCamlPro               *)
(*                                                                        *)
(*   Copyright 2024 OCamlPro SAS                                          *)
(*   Copyright 2024 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type cont_kind = Normal of Variable.t list

type should_preserve_direct_calls =
  | Yes
  | No
  | Auto

type t =
  { parent : Rev_expr.rev_expr_holed;
    conts : cont_kind Continuation.Map.t;
    current_code_id : Code_id.t option;
    should_preserve_direct_calls : should_preserve_direct_calls;
    le_monde_exterieur : Name.t;
    all_constants : Name.t;
    region_scope : region_scope;
    enclosing_region_scopes : Code_id_or_name.t list;
    return_continuation : Continuation.t;
    exn_continuation : Continuation.t
  }

and region_scope =
  | No_region_scope
  | Toplevel
  | Scope of Code_id_or_name.t

let create ~parent ~conts ~current_code_id ~should_preserve_direct_calls
    ~le_monde_exterieur ~all_constants ~region_scope ~return_continuation
    ~exn_continuation =
  { parent;
    conts;
    current_code_id;
    should_preserve_direct_calls;
    le_monde_exterieur;
    all_constants;
    region_scope;
    enclosing_region_scopes =
      (match region_scope with
      | No_region_scope | Toplevel -> []
      | Scope scope -> [scope]);
    return_continuation;
    exn_continuation
  }

let region_scope t =
  match t.region_scope with
  | No_region_scope | Toplevel -> None
  | Scope scope -> Some scope

let enclosing_region_scopes t = t.enclosing_region_scopes

let return_continuation t = t.return_continuation

let exn_continuation t = t.exn_continuation

let enter_recursive_handler t ~scope =
  match t.region_scope with
  | No_region_scope -> t
  | Toplevel | Scope _ ->
    let scope = Code_id_or_name.var scope in
    { t with
      region_scope = Scope scope;
      enclosing_region_scopes = scope :: t.enclosing_region_scopes
    }

let all_continuation_params t =
  Continuation.Map.fold (fun _ (Normal params) acc -> params @ acc) t.conts []

let parent t = t.parent

let current_code_id t = t.current_code_id

let should_preserve_direct_calls t = t.should_preserve_direct_calls

let le_monde_exterieur t = t.le_monde_exterieur

let all_constants t = t.all_constants

let with_parent t parent = { t with parent }

let find_cont t cont =
  match Continuation.Map.find_opt cont t.conts with
  | Some cont_kind -> cont_kind
  | None ->
    Misc.fatal_errorf "[Env.find_cont]: continuation %a not found in env"
      Continuation.print cont

let add_cont t cont cont_kind =
  { t with conts = Continuation.Map.add cont cont_kind t.conts }
