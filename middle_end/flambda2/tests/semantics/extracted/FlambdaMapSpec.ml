open BinNums
open BinPos
open Datatypes
open List
open ListDef

(** val among : positive -> positive list -> bool **)

let among name names = existsb (Pos.eqb name) names

(** val all_among : positive list -> positive list -> bool **)

let all_among names allowed = forallb (fun name -> among name allowed) names

(** val without : positive list -> positive list -> positive list **)

let without bound names = filter (fun name -> negb (among name bound)) names

(** val inter : positive list -> positive list -> positive list **)

let inter names names' = filter (fun name -> among name names') names

(** val distinct : positive list -> bool **)

let rec distinct = function
  | [] -> true
  | name :: names0 -> negb (among name names0) && distinct names0

(** val dedup : positive list -> positive list **)

let rec dedup = function
  | [] -> []
  | name :: names0 -> name :: without (name :: []) (dedup names0)

type 'a finite_map = (positive * 'a) list

(** val lookup : positive -> (positive * 'a1) list -> 'a1 option **)

let rec lookup name = function
  | [] -> None
  | p :: bindings0 ->
    let bound, a = p in
    if Pos.eqb name bound then Some a else lookup name bindings0

(** val is_bound : positive -> 'a1 finite_map -> bool **)

let is_bound name bindings =
  match lookup name bindings with Some _ -> true | None -> false

(** val unbind : positive -> 'a1 finite_map -> 'a1 finite_map **)

let unbind name bindings =
  filter (fun binding -> negb (Pos.eqb name (fst binding))) bindings

(** val map_values : ('a1 -> 'a2) -> 'a1 finite_map -> 'a2 finite_map **)

let map_values f bindings =
  map (fun binding -> fst binding, f (snd binding)) bindings

(** val domain : 'a1 finite_map -> positive list **)

let domain bindings = dedup (map fst bindings)

(** val tabulate : (positive -> 'a1 option) -> positive list -> 'a1 finite_map **)

let tabulate f names =
  flat_map
    (fun name -> match f name with Some a -> (name, a) :: [] | None -> [])
    names

(** val compact : 'a1 finite_map -> 'a1 finite_map **)

let compact bindings =
  tabulate (fun name -> lookup name bindings) (domain bindings)

(** val filter_bindings : (positive -> 'a1 -> bool) -> 'a1 finite_map -> 'a1
    finite_map **)

let filter_bindings keep bindings =
  tabulate
    (fun name ->
      match lookup name bindings with
      | Some a -> if keep name a then Some a else None
      | None -> None)
    (domain bindings)

(** val merge : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 finite_map ->
    'a2 finite_map -> 'a3 finite_map **)

let merge f bindings bindings' =
  tabulate
    (fun name -> f (lookup name bindings) (lookup name bindings'))
    (dedup (app (map fst bindings) (map fst bindings')))

(** val union_with : ('a1 -> 'a1 -> 'a1) -> 'a1 finite_map -> 'a1 finite_map ->
    'a1 finite_map **)

let union_with f bindings bindings' =
  merge
    (fun a a' ->
      match a with
      | Some a0 -> (
        match a' with Some a'0 -> Some (f a0 a'0) | None -> Some a0)
      | None -> a')
    bindings bindings'

(** val inter_with : ('a1 -> 'a2 -> 'a3) -> 'a1 finite_map -> 'a2 finite_map ->
    'a3 finite_map **)

let inter_with f bindings bindings' =
  merge
    (fun a b ->
      match a with
      | Some a0 -> ( match b with Some b0 -> Some (f a0 b0) | None -> None)
      | None -> None)
    bindings bindings'

module Keyed = struct
  type ('k, 'a) finite_map = ('k * 'a) list

  (** val among : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

  let among eqb0 key keys = existsb (eqb0 key) keys

  (** val all_among : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

  let all_among eqb0 keys allowed =
    forallb (fun key -> among eqb0 key allowed) keys

  (** val distinct : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

  let rec distinct eqb0 = function
    | [] -> true
    | key :: keys0 -> negb (among eqb0 key keys0) && distinct eqb0 keys0

  (** val same_keys_b : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

  let same_keys_b eqb0 keys keys' =
    all_among eqb0 keys keys' && all_among eqb0 keys' keys

  (** val is_empty : 'a1 list -> bool **)

  let is_empty = function [] -> true | _ :: _ -> false

  (** val lookup : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 * 'a2) list -> 'a2 option
      **)

  let rec lookup eqb0 key = function
    | [] -> None
    | p :: bindings0 ->
      let bound, a = p in
      if eqb0 key bound then Some a else lookup eqb0 key bindings0

  (** val is_bound : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1, 'a2) finite_map ->
      bool **)

  let is_bound eqb0 key bindings =
    match lookup eqb0 key bindings with Some _ -> true | None -> false

  (** val for_all_bindings_b : ('a1 -> 'a1 -> bool) -> ('a1 -> 'a2 -> bool) ->
      ('a1, 'a2) finite_map -> bool **)

  let for_all_bindings_b eqb0 p bindings =
    let rec for_all_bindings_b0 seen = function
      | [] -> true
      | p0 :: bindings1 ->
        let key, a = p0 in
        (among eqb0 key seen || p key a)
        && for_all_bindings_b0 (key :: seen) bindings1
    in
    for_all_bindings_b0 [] bindings

  (** val at_binding_b : ('a1 -> 'a1 -> bool) -> ('a2 -> bool) -> 'a1 -> ('a1,
      'a2) finite_map -> bool **)

  let rec at_binding_b eqb0 p key = function
    | [] -> true
    | p0 :: bindings0 ->
      let bound, a = p0 in
      if eqb0 key bound then p a else at_binding_b eqb0 p key bindings0
end
