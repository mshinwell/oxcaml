# The port of Simplify: progress

Made by `make table` (tools/progress.sh); do not edit. One line for each
file of `middle_end/flambda2/simplify/`. `defs`: the compiler's definitions
at the left margin; `ported`: those that the Rocq file defines; `gaps`:
the marks PORT-GAP by kind; `OCaml`: how the extracted file type-checks
(strict: against the whole interface; overlay: in the place of the
compiler's own definitions; alone: no interface).

| file | lines | defs | ported | gaps | Rocq | OCaml |
|---|---:|---:|---:|---|---|---|
| `apply_cont_rewrite.ml` | 307 | 13 | 0 | - | - | - |
| `are_lifting_conts.ml` | 68 | 5 | 0 | - | - | - |
| `common_subexpression_elimination.ml` | 481 | 5 | 0 | - | - | - |
| `comparison_result.ml` | 86 | 3 | 0 | - | - | - |
| `continuation_extra_params_and_args.ml` | 198 | 10 | 0 | - | - | - |
| `continuation_in_env.ml` | 79 | 2 | 0 | - | - | - |
| `continuation_shortcut.ml` | 63 | 5 | 0 | - | - | - |
| `env/closure_info.ml` | 76 | 5 | 0 | - | - | - |
| `env/continuation_uses.ml` | 158 | 17 | 0 | - | - | - |
| `env/continuation_uses_env.ml` | 167 | 16 | 0 | - | - | - |
| `env/continuation_uses_env_intf.ml` | 39 | 0 | 0 | - | - | - |
| `env/downwards_acc.ml` | 342 | 63 | 0 | - | - | - |
| `env/downwards_env.ml` | 945 | 102 | 0 | - | - | - |
| `env/one_continuation_use.ml` | 49 | 7 | 0 | - | - | - |
| `env/replay_history.ml` | 230 | 14 | 0 | - | - | - |
| `env/upwards_acc.ml` | 183 | 40 | 0 | - | - | - |
| `env/upwards_env.ml` | 211 | 21 | 0 | - | - | - |
| `expr_builder.ml` | 800 | 25 | 0 | - | - | - |
| `flow/control_flow_graph.ml` | 476 | 9 | 0 | - | - | - |
| `flow/data_flow_graph.ml` | 451 | 11 | 0 | - | - | - |
| `flow/dominator_graph.ml` | 359 | 14 | 0 | - | - | - |
| `flow/flow.ml` | 16 | 0 | 0 | - | - | - |
| `flow/flow_acc.ml` | 638 | 32 | 0 | - | - | - |
| `flow/flow_analysis.ml` | 211 | 7 | 0 | - | - | - |
| `flow/flow_types.ml` | 363 | 0 | 0 | - | - | - |
| `flow/mutable_unboxing.ml` | 716 | 21 | 0 | - | - | - |
| `inlining/call_site_inlining_decision.ml` | 464 | 7 | 0 | - | - | - |
| `inlining/inlining_transforms.ml` | 181 | 3 | 0 | - | - | - |
| `join_points.ml` | 442 | 7 | 0 | - | - | - |
| `lifted_cont_params.ml` | 88 | 11 | 0 | - | - | - |
| `lifting/lifted_constant.ml` | 324 | 17 | 0 | - | - | - |
| `lifting/lifted_constant_state.ml` | 203 | 13 | 0 | - | - | - |
| `lifting/reification.ml` | 199 | 3 | 0 | - | - | - |
| `loopify_state.ml` | 26 | 3 | 0 | - | - | - |
| `named_rewrite.ml` | 48 | 2 | 0 | - | - | - |
| `non_constructed_code.ml` | 41 | 6 | 0 | - | - | - |
| `non_recursive_handler.ml` | 75 | 5 | 0 | - | - | - |
| `number_adjuncts.ml` | 1035 | 2 | 0 | - | - | - |
| `one_recursive_handler.ml` | 30 | 3 | 0 | - | - | - |
| `original_handlers.ml` | 97 | 6 | 0 | - | - | - |
| `rebuilt_expr.ml` | 753 | 22 | 0 | - | - | - |
| `rebuilt_static_const.ml` | 522 | 44 | 0 | - | - | - |
| `simplified_expr.ml` | 185 | 14 | 0 | - | - | - |
| `simplified_named.ml` | 100 | 6 | 0 | - | - | - |
| `simplify.ml` | 99 | 1 | 0 | - | - | - |
| `simplify_apply_cont_expr.ml` | 199 | 3 | 3 | papp:1 | yes | strict |
| `simplify_apply_expr.ml` | 1539 | 21 | 0 | - | - | - |
| `simplify_binary_primitive.ml` | 1270 | 12 | 0 | - | - | - |
| `simplify_coercion.ml` | 25 | 1 | 0 | - | - | - |
| `simplify_common.ml` | 479 | 10 | 0 | - | - | - |
| `simplify_expr.ml` | 231 | 7 | 7 | loose:1 type:2 papp:2 | yes | strict |
| `simplify_extcall.ml` | 239 | 9 | 0 | - | - | - |
| `simplify_import.ml` | 67 | 1 | 1 | none | yes | strict |
| `simplify_let_cont_expr.ml` | 2039 | 36 | 0 | - | - | - |
| `simplify_let_expr.ml` | 461 | 6 | 0 | - | - | - |
| `simplify_named.ml` | 333 | 4 | 0 | - | - | - |
| `simplify_named_result.ml` | 63 | 8 | 0 | - | - | - |
| `simplify_nullary_primitive.ml` | 77 | 1 | 0 | - | - | - |
| `simplify_primitive.ml` | 235 | 4 | 0 | - | - | - |
| `simplify_primitive_result.ml` | 66 | 8 | 0 | - | - | - |
| `simplify_quaternary_primitive.ml` | 112 | 4 | 0 | - | - | - |
| `simplify_rec_info_expr.ml` | 164 | 8 | 0 | - | - | - |
| `simplify_set_of_closures.ml` | 1230 | 15 | 0 | - | - | - |
| `simplify_set_of_closures_context.ml` | 375 | 18 | 0 | - | - | - |
| `simplify_simple.ml` | 65 | 4 | 0 | - | - | - |
| `simplify_static_const.ml` | 483 | 6 | 0 | - | - | - |
| `simplify_switch_expr.ml` | 1096 | 26 | 0 | - | - | - |
| `simplify_ternary_primitive.ml` | 116 | 8 | 0 | - | - | - |
| `simplify_unary_primitive.ml` | 1106 | 35 | 0 | - | - | - |
| `simplify_variadic_primitive.ml` | 186 | 4 | 0 | - | - | - |
| `specialization_cost.ml` | 202 | 12 | 0 | - | - | - |
| `unboxing/build_unboxing_denv.ml` | 291 | 3 | 0 | - | - | - |
| `unboxing/is_unboxing_beneficial.ml` | 98 | 2 | 0 | - | - | - |
| `unboxing/optimistic_unboxing_decision.ml` | 228 | 12 | 0 | - | - | - |
| `unboxing/unbox_continuation_params.ml` | 203 | 4 | 0 | - | - | - |
| `unboxing/unboxers.ml` | 260 | 0 | 0 | - | - | - |
| `unboxing/unboxing_epa.ml` | 553 | 15 | 0 | - | - | - |
| `unboxing/unboxing_types.ml` | 185 | 9 | 0 | - | - | - |
| **total: 3 files of 78** | 26900 | 938 | 11 | 6 marks | 3 | 3 |

Gaps by kind, all files:

- unported: 0
- partial: 0
- loose: 1
- type: 2
- verbatim: 0
- init: 0
- order: 0
- decl: 0
- papp: 3
