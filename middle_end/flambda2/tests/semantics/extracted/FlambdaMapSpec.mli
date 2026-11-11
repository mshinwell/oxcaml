open BinNums
open BinPos
open Datatypes
open List
open ListDef

val among : positive -> positive list -> bool

val all_among : positive list -> positive list -> bool

val without : positive list -> positive list -> positive list

val inter : positive list -> positive list -> positive list

val distinct : positive list -> bool

val dedup : positive list -> positive list

type 'a finite_map = (positive * 'a) list

val lookup : positive -> (positive * 'a1) list -> 'a1 option

val is_bound : positive -> 'a1 finite_map -> bool

val unbind : positive -> 'a1 finite_map -> 'a1 finite_map

val map_values : ('a1 -> 'a2) -> 'a1 finite_map -> 'a2 finite_map

val domain : 'a1 finite_map -> positive list

val tabulate : (positive -> 'a1 option) -> positive list -> 'a1 finite_map

val compact : 'a1 finite_map -> 'a1 finite_map

val filter_bindings :
  (positive -> 'a1 -> bool) -> 'a1 finite_map -> 'a1 finite_map

val merge :
  ('a1 option -> 'a2 option -> 'a3 option) ->
  'a1 finite_map ->
  'a2 finite_map ->
  'a3 finite_map

val union_with :
  ('a1 -> 'a1 -> 'a1) -> 'a1 finite_map -> 'a1 finite_map -> 'a1 finite_map

val inter_with :
  ('a1 -> 'a2 -> 'a3) -> 'a1 finite_map -> 'a2 finite_map -> 'a3 finite_map

module Keyed : sig
  type ('k, 'a) finite_map = ('k * 'a) list

  val among : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

  val all_among : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

  val distinct : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

  val same_keys_b : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

  val is_empty : 'a1 list -> bool

  val lookup : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 * 'a2) list -> 'a2 option

  val is_bound : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1, 'a2) finite_map -> bool

  val for_all_bindings_b :
    ('a1 -> 'a1 -> bool) ->
    ('a1 -> 'a2 -> bool) ->
    ('a1, 'a2) finite_map ->
    bool

  val at_binding_b :
    ('a1 -> 'a1 -> bool) ->
    ('a2 -> bool) ->
    'a1 ->
    ('a1, 'a2) finite_map ->
    bool
end
