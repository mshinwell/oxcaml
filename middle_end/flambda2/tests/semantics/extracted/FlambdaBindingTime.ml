open BinInt
open BinNums

module Name_mode = struct
  type t =
    | Normal
    | Phantom
    | In_types

  (** val normal : t **)

  let normal = Normal

  (** val in_types : t **)

  let in_types = In_types

  (** val compare_partial_order : t -> t -> coq_Z option **)

  let compare_partial_order t1 t2 =
    match t1 with
    | Normal -> ( match t2 with Normal -> Some Z0 | _ -> Some (Zpos Coq_xH))
    | Phantom -> (
      match t2 with
      | Normal -> Some (Zneg Coq_xH)
      | Phantom -> Some Z0
      | In_types -> Some (Zpos Coq_xH))
    | In_types -> (
      match t2 with In_types -> Some Z0 | _ -> Some (Zneg Coq_xH))

  (** val equal : t -> t -> bool **)

  let equal t1 t2 =
    match t1 with
    | Normal -> ( match t2 with Normal -> true | _ -> false)
    | Phantom -> ( match t2 with Phantom -> true | _ -> false)
    | In_types -> ( match t2 with In_types -> true | _ -> false)
end

module Binding_time = struct
  module Coq__1 = struct
    type t = coq_Z
  end

  include Coq__1

  (** val strictly_earlier : t -> t -> bool **)

  let strictly_earlier = Z.ltb

  (** val consts : t **)

  let consts = Z0

  (** val symbols : t **)

  let symbols = Zpos Coq_xH

  (** val imported_variables : t **)

  let imported_variables = Zpos (Coq_xO Coq_xH)

  (** val earliest_var : t **)

  let earliest_var = Zpos (Coq_xI Coq_xH)

  (** val succ : t -> t **)

  let succ t0 = Z.add t0 (Zpos Coq_xH)

  (** val equal : t -> t -> bool **)

  let equal = Z.eqb

  module With_name_mode = struct
    type t =
      { binding_time : Coq__1.t;
        name_mode : Name_mode.t
      }

    (** val binding_time : t -> Coq__1.t **)

    let binding_time t0 = t0.binding_time

    (** val name_mode : t -> Name_mode.t **)

    let name_mode t0 = t0.name_mode

    (** val symbols : t **)

    let symbols = { binding_time = symbols; name_mode = Name_mode.normal }

    (** val consts : t **)

    let consts = { binding_time = consts; name_mode = Name_mode.normal }

    (** val imported_variables : t **)

    let imported_variables =
      { binding_time = imported_variables; name_mode = Name_mode.in_types }

    (** val scoped_name_mode : t -> Coq__1.t -> Name_mode.t **)

    let scoped_name_mode t0 min_binding_time =
      if
        Z.ltb t0.binding_time earliest_var
        || Z.leb min_binding_time t0.binding_time
      then t0.name_mode
      else Name_mode.in_types
  end
end
