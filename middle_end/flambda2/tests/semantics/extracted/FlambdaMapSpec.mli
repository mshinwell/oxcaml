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

  val without : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> 'a1 list

  val inter : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> 'a1 list

  val distinct : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

  val dedup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

  val same_keys_b : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

  val is_empty : 'a1 list -> bool

  val get_singleton : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 option

  val lookup : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1 * 'a2) list -> 'a2 option

  val is_bound : ('a1 -> 'a1 -> bool) -> 'a1 -> ('a1, 'a2) finite_map -> bool

  val unbind :
    ('a1 -> 'a1 -> bool) ->
    'a1 ->
    ('a1, 'a2) finite_map ->
    ('a1, 'a2) finite_map

  val map_values :
    ('a2 -> 'a3) -> ('a1, 'a2) finite_map -> ('a1, 'a3) finite_map

  val domain : ('a1 -> 'a1 -> bool) -> ('a1, 'a2) finite_map -> 'a1 list

  val tabulate : ('a1 -> 'a2 option) -> 'a1 list -> ('a1, 'a2) finite_map

  val compact :
    ('a1 -> 'a1 -> bool) -> ('a1, 'a2) finite_map -> ('a1, 'a2) finite_map

  val filter_bindings :
    ('a1 -> 'a1 -> bool) ->
    ('a1 -> 'a2 -> bool) ->
    ('a1, 'a2) finite_map ->
    ('a1, 'a2) finite_map

  val merge :
    ('a1 -> 'a1 -> bool) ->
    ('a2 option -> 'a3 option -> 'a4 option) ->
    ('a1, 'a2) finite_map ->
    ('a1, 'a3) finite_map ->
    ('a1, 'a4) finite_map

  val get_singleton_binding :
    ('a1 -> 'a1 -> bool) -> ('a1, 'a2) finite_map -> ('a1 * 'a2) option

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

  val fold2_on :
    ('a1 -> 'a1 -> bool) ->
    'a1 list ->
    ('a1 -> 'a2 option -> 'a3 option -> 'a4 -> 'a4) ->
    ('a1, 'a2) finite_map ->
    ('a1, 'a3) finite_map ->
    'a4 ->
    'a4

  val keys_of_both :
    ('a1 -> 'a1 -> bool) ->
    ('a1, 'a2) finite_map ->
    ('a1, 'a3) finite_map ->
    'a1 list

  val merge_fold_on :
    ('a1 -> 'a1 -> bool) ->
    'a1 list ->
    ('a1 -> 'a2 option -> 'a3 option -> 'a5 -> 'a4 option * 'a5) ->
    ('a1, 'a2) finite_map ->
    ('a1, 'a3) finite_map ->
    'a5 ->
    ('a1, 'a4) finite_map * 'a5

  val tabulate_fold_opt :
    ('a1 -> 'a3 -> ('a2 option * 'a3) option) ->
    'a1 list ->
    'a3 ->
    (('a1, 'a2) finite_map * 'a3) option

  val filter_map_fold_on :
    ('a1 -> 'a1 -> bool) ->
    'a1 list ->
    ('a1 -> 'a2 -> 'a4 -> ('a3 option * 'a4) option) ->
    ('a1, 'a2) finite_map ->
    'a4 ->
    (('a1, 'a3) finite_map * 'a4) option

  val filter_map_fold :
    ('a1 -> 'a1 -> bool) ->
    ('a1 -> 'a2 -> 'a4 -> ('a3 option * 'a4) option) ->
    ('a1, 'a2) finite_map ->
    'a4 ->
    (('a1, 'a3) finite_map * 'a4) option
end
