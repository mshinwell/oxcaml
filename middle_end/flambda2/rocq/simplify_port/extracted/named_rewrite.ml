(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Nathanaëlle Courant, Guillaume Bury and Pierre Chambart, OCamlPro    *)
(*                                                                        *)
(*   Copyright 2022--2022 OCamlPro SAS                                    *)
(*   Copyright 2022--2022 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Named_rewrite.v, which follows
   middle_end/flambda2/simplify/named_rewrite.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad

module Prim_rewrite = struct
  type t =
    | Remove_prim
    | Invalid of Flambda_kind.t
    | Replace_by_binding of
        { var : Variable.t;
          bound_to : Simple.t
        }

  (** val print : Format.formatter -> t -> unit coq_M **)

  let print ppf t0 =
    (fun f__1 f__2 f__3 x__0 ->
      match x__0 with
      | Remove_prim -> f__1 ()
      | Invalid x__1 -> f__2 x__1
      | Replace_by_binding { var = x__1; bound_to = x__2 } -> f__3 x__1 x__2)
      (fun _ -> Format.fprintf ppf "Remove_prim")
      (fun _ -> Format.fprintf ppf "Invalid")
      (fun var bound_to ->
        Format.fprintf ppf "Replace_by_binding { %a = %a }" Variable.print var
          Simple.print bound_to)
      t0

  (** val invalid : Flambda_kind.t -> t coq_M **)

  let invalid k = Invalid k

  (** val remove_prim : t **)

  let remove_prim = Remove_prim

  (** val replace_by_binding : Variable.t -> Simple.t -> t coq_M **)

  let replace_by_binding var bound_to =
    (fun (x__1, x__2) -> Replace_by_binding { var = x__1; bound_to = x__2 })
      (var, bound_to)
end

type t = Prim_rewrite of Prim_rewrite.t

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf = function
  | Prim_rewrite prim_rewrite0 -> Prim_rewrite.print ppf prim_rewrite0

(** val prim_rewrite : Prim_rewrite.t -> t coq_M **)

let prim_rewrite prim_rewrite0 = Prim_rewrite prim_rewrite0
