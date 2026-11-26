# The port of Simplify: progress

Made by `make table` (tools/progress.sh); do not edit. One line for each
file of `middle_end/flambda2/simplify/`. `defs`: the compiler's definitions
at the left margin; `ported`: those that the Rocq file defines; `gaps`:
the marks PORT-GAP by kind; `OCaml`: how the extracted file type-checks
(strict: against the whole interface; overlay: in the place of the
compiler's own definitions; alone: no interface).

| file | lines | defs | ported | gaps | Rocq | OCaml |
|---|---:|---:|---:|---|---|---|
| `apply_cont_rewrite.ml` | 307 | 13 | 13 | loose:1 | yes | strict |
| `are_lifting_conts.ml` | 68 | 5 | 5 | loose:1 | yes | strict |
| `common_subexpression_elimination.ml` | 481 | 5 | 5 | loose:8 | yes | strict |
| `comparison_result.ml` | 86 | 3 | 3 | loose:3 | yes | strict |
| `continuation_extra_params_and_args.ml` | 198 | 10 | 10 | loose:2 | yes | strict |
| `continuation_in_env.ml` | 79 | 2 | 2 | loose:1 | yes | strict |
| `continuation_shortcut.ml` | 63 | 5 | 5 | loose:2 | yes | strict |
| `env/closure_info.ml` | 76 | 5 | 5 | loose:1 | yes | strict |
| `env/continuation_uses.ml` | 158 | 17 | 17 | loose:3 | yes | strict |
| `env/continuation_uses_env.ml` | 167 | 16 | 16 | loose:2 record-order:1 | yes | strict |
| `env/continuation_uses_env_intf.ml` | 39 | 0 | 0 | loose:1 | yes | alone |
| `env/downwards_acc.ml` | 342 | 63 | 63 | loose:4 verbatim:1 record-order:1 | yes | strict |
| `env/downwards_env.ml` | 945 | 102 | 102 | loose:9 type:1 verbatim:3 papp:1 record-order:2 | yes | strict |
| `env/one_continuation_use.ml` | 49 | 7 | 7 | loose:3 | yes | strict |
| `env/replay_history.ml` | 230 | 14 | 14 | loose:1 | yes | strict |
| `env/upwards_acc.ml` | 183 | 40 | 40 | loose:2 | yes | strict |
| `env/upwards_env.ml` | 211 | 21 | 21 | loose:2 type:1 | yes | strict |
| `expr_builder.ml` | 800 | 25 | 25 | loose:8 | yes | strict |
| `flow/control_flow_graph.ml` | 476 | 9 | 9 | verbatim:1 | yes | strict |
| `flow/data_flow_graph.ml` | 451 | 11 | 11 | loose:5 | yes | strict |
| `flow/dominator_graph.ml` | 359 | 14 | 14 | none | yes | strict |
| `flow/flow.ml` | 16 | 0 | 0 | none | yes | strict |
| `flow/flow_acc.ml` | 638 | 32 | 32 | loose:2 | yes | strict |
| `flow/flow_analysis.ml` | 211 | 7 | 4 | verbatim:1 init:3 papp:1 | yes | strict |
| `flow/flow_types.ml` | 363 | 0 | 0 | loose:8 | yes | strict |
| `flow/mutable_unboxing.ml` | 716 | 21 | 21 | loose:1 record-order:2 | yes | strict |
| `inlining/call_site_inlining_decision.ml` | 464 | 7 | 7 | loose:4 type:1 init:1 | yes | strict |
| `inlining/inlining_transforms.ml` | 181 | 3 | 3 | loose:3 | yes | strict |
| `join_points.ml` | 442 | 7 | 7 | loose:4 verbatim:1 | yes | strict |
| `lifted_cont_params.ml` | 88 | 11 | 11 | loose:1 | yes | strict |
| `lifting/lifted_constant.ml` | 324 | 17 | 17 | loose:7 type:1 verbatim:2 record-order:4 | yes | strict |
| `lifting/lifted_constant_state.ml` | 203 | 13 | 13 | loose:2 | yes | strict |
| `lifting/reification.ml` | 199 | 3 | 3 | loose:1 | yes | strict |
| `loopify_state.ml` | 26 | 3 | 3 | none | yes | strict |
| `named_rewrite.ml` | 48 | 2 | 2 | none | yes | strict |
| `non_constructed_code.ml` | 41 | 6 | 6 | none | yes | strict |
| `non_recursive_handler.ml` | 75 | 5 | 5 | loose:1 | yes | strict |
| `number_adjuncts.ml` | 1035 | 2 | 2 | loose:3 init:3 | yes | strict |
| `one_recursive_handler.ml` | 30 | 3 | 3 | none | yes | strict |
| `original_handlers.ml` | 97 | 6 | 6 | loose:2 | yes | strict |
| `rebuilt_expr.ml` | 753 | 22 | 21 | loose:9 type:1 init:2 decl:1 record-order:1 | yes | strict |
| `rebuilt_static_const.ml` | 522 | 44 | 44 | loose:5 type:1 init:2 record-order:5 | yes | strict |
| `simplified_expr.ml` | 185 | 9 | 9 | verbatim:1 | yes | strict |
| `simplified_named.ml` | 100 | 6 | 6 | loose:1 | yes | strict |
| `simplify.ml` | 99 | 1 | 1 | none | yes | strict |
| `simplify_apply_cont_expr.ml` | 199 | 3 | 3 | none | yes | strict |
| `simplify_apply_expr.ml` | 1539 | 21 | 21 | loose:5 | yes | strict |
| `simplify_binary_primitive.ml` | 1270 | 12 | 12 | loose:21 verbatim:1 init:1 | yes | strict |
| `simplify_coercion.ml` | 25 | 1 | 1 | none | yes | strict |
| `simplify_common.ml` | 479 | 10 | 10 | loose:2 | yes | strict |
| `simplify_expr.ml` | 231 | 7 | 7 | loose:1 type:2 | yes | strict |
| `simplify_extcall.ml` | 239 | 9 | 9 | loose:2 | yes | strict |
| `simplify_import.ml` | 67 | 1 | 1 | none | yes | strict |
| `simplify_let_cont_expr.ml` | 2039 | 36 | 36 | loose:2 type:5 record-order:2 | yes | strict |
| `simplify_let_expr.ml` | 461 | 6 | 6 | loose:2 | yes | strict |
| `simplify_named.ml` | 333 | 4 | 4 | loose:2 | yes | strict |
| `simplify_named_result.ml` | 63 | 8 | 8 | loose:1 record-order:1 | yes | strict |
| `simplify_nullary_primitive.ml` | 77 | 1 | 1 | none | yes | strict |
| `simplify_primitive.ml` | 235 | 4 | 4 | none | yes | strict |
| `simplify_primitive_result.ml` | 66 | 8 | 8 | loose:1 | yes | strict |
| `simplify_quaternary_primitive.ml` | 112 | 4 | 4 | none | yes | alone |
| `simplify_rec_info_expr.ml` | 164 | 8 | 8 | loose:4 | yes | strict |
| `simplify_set_of_closures.ml` | 1230 | 15 | 15 | loose:3 record-order:2 | yes | strict |
| `simplify_set_of_closures_context.ml` | 375 | 18 | 18 | loose:1 verbatim:1 | yes | strict |
| `simplify_simple.ml` | 65 | 4 | 4 | none | yes | strict |
| `simplify_static_const.ml` | 483 | 6 | 6 | loose:1 | yes | strict |
| `simplify_switch_expr.ml` | 1096 | 26 | 26 | loose:10 type:2 record-order:1 | yes | strict |
| `simplify_ternary_primitive.ml` | 116 | 8 | 8 | none | yes | strict |
| `simplify_unary_primitive.ml` | 1106 | 35 | 35 | loose:16 | yes | strict |
| `simplify_variadic_primitive.ml` | 186 | 4 | 4 | loose:2 | yes | strict |
| `specialization_cost.ml` | 202 | 12 | 12 | none | yes | strict |
| `unboxing/build_unboxing_denv.ml` | 291 | 3 | 3 | type:1 | yes | strict |
| `unboxing/is_unboxing_beneficial.ml` | 98 | 2 | 2 | type:1 | yes | strict |
| `unboxing/optimistic_unboxing_decision.ml` | 228 | 12 | 12 | loose:3 | yes | strict |
| `unboxing/unbox_continuation_params.ml` | 203 | 4 | 4 | loose:2 | yes | strict |
| `unboxing/unboxers.ml` | 260 | 0 | 0 | loose:1 init:10 record-order:1 | yes | strict |
| `unboxing/unboxing_epa.ml` | 553 | 15 | 15 | loose:1 | yes | strict |
| `unboxing/unboxing_types.ml` | 185 | 6 | 6 | type:1 verbatim:2 | yes | strict |
| **total: 78 files of 78** | 26900 | 930 | 926 | 276 marks | 78 | 78 |

Gaps by kind, the ported files:

- unported: 0
- partial: 0
- loose: 196
- type: 18
- verbatim: 14
- init: 22
- order: 0
- decl: 1
- papp: 2
- record-order: 23
- update: 0

The marks of the other `.v` files of the folder (`decl/`, which
`tools/declgen` writes; the kit, `monad/`). They are not in the table
and not in the numbers above:

- `decl/`: type: 6
- `monad/`: loose: 1
