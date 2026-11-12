open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaBlockLoadSpec
open FlambdaCompareSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaSemanticsSpec
open FlambdaUnboxParamsSpec
open FlambdaUnboxSpec
open FlambdaUnusedContsSpec
open List
open ListDef
open Nat
open OxCamlOption

val dummy_of : bool -> unary_primitive -> flambda_kind -> const

val no_value_on : facts -> unary_primitive -> simple -> bool

val made_field :
  facts -> unary_primitive -> flambda_kind -> simple -> simple option

val made_number :
  facts -> unary_primitive -> flambda_kind -> simple -> simple option

val certain_projection :
  facts -> unary_primitive -> flambda_kind -> simple -> simple option

val known_immediates : variable list -> simple list -> (variable * coq_Z) list

val forget_immediates :
  variable list -> (variable * coq_Z) list -> (variable * coq_Z) list

val take_arms : (variable * coq_Z) list -> expr -> expr

val never_reads : (variable * coq_Z) list -> expr -> expr -> bool

val only_of :
  variable list -> (variable * coq_Z) list -> (variable * coq_Z) list

val extend_args_certain :
  bool ->
  variable list ->
  variable list ->
  expr ->
  expr ->
  facts ->
  nat ->
  unary_primitive ->
  flambda_kind ->
  simple list ->
  simple list option

type read =
  { read_variable : variable;
    read_kind : flambda_kind;
    read_primitive : unary_primitive;
    read_position : nat;
    read_without : expr
  }

val reads_tag : unary_primitive -> bool

val reads_constant_constructor : unary_primitive -> bool

val reads_is_int : unary_primitive -> bool

val reads_contents : unary_primitive -> bool

val reads_any : unary_primitive -> bool

val param_read :
  (unary_primitive -> bool) ->
  variable list ->
  variable list ->
  variable ->
  named ->
  (unary_primitive * nat) option

val head_read : variable list -> expr -> read option

val load_read : named -> (variable * coq_Z) option

val loads_above : coq_Z -> unary_primitive -> bool

val first_read :
  (unary_primitive -> bool) ->
  variable list ->
  variable list ->
  expr ->
  read option

val next_read : variable list -> expr -> read option

val lets_in : expr -> nat

val unbox_read :
  (facts -> simple list -> simple list option) ->
  facts ->
  continuation ->
  variable list ->
  handler_metadata ->
  expr ->
  expr ->
  read ->
  (((variable list * handler_metadata) * expr) * expr) option

val tested_is_int : variable list -> nat -> expr -> bool

val reads_test : unary_primitive -> bool

val boxes_of : nat -> (nat * nat list) list -> nat list

val tests_of :
  nat -> (variable * nat) list -> (nat * nat list) list -> variable list

val unbox_reads :
  nat ->
  facts ->
  continuation ->
  (variable * nat) list ->
  (nat * nat list) list ->
  variable list ->
  handler_metadata ->
  expr ->
  expr ->
  expr

val unbox_variants_knowing : facts -> expr -> expr
