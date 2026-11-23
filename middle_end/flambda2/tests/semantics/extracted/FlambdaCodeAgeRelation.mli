open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaTypeGrammar

module Code_age_relation : sig
  type t = (code_id * code_id) list

  val empty : t

  val get_older_version_of : t -> code_id -> code_id option

  val add : t -> code_id -> code_id -> t

  val has_older_version_in :
    (code_id -> 'a1) ->
    'a1 ->
    ('a1 -> 'a1 -> bool) ->
    nat ->
    t ->
    ('a1 -> t option) ->
    code_id ->
    code_id list ->
    bool Or_unknown.t option

  val should_keep_id :
    (code_id -> 'a1) ->
    'a1 ->
    ('a1 -> 'a1 -> bool) ->
    nat ->
    t ->
    ('a1 -> t option) ->
    code_id list ->
    code_id ->
    bool option

  val filter_ids :
    (code_id -> bool option) -> code_id list -> code_id list option

  val meet_set :
    (code_id -> 'a1) ->
    'a1 ->
    ('a1 -> 'a1 -> bool) ->
    nat ->
    t ->
    ('a1 -> t option) ->
    code_id list ->
    code_id list ->
    code_id list Or_bottom.t option

  val meet :
    (code_id -> 'a1) ->
    'a1 ->
    ('a1 -> 'a1 -> bool) ->
    nat ->
    t ->
    ('a1 -> t option) ->
    code_id ->
    code_id ->
    code_id or_unknown_or_bottom option
end
