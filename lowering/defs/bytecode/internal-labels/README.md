# Internal-label witnesses (#546, a05-07)

Each source has an internal function whose name equals a label the lowering
makes itself, or starts with a prefix the whitelist used to exclude. Before
a05-07 an internal function's Venom label was its bare source name, so these
collided with a codegen label (`revert`, `code_end`: miscompiled), an
external entry label (`"fn_" ++ name`) or the unit entry (`__entry`: both
`compile_vyper = NONE`). Internal functions are now labelled
`internal_fn_label` (`internal <name>(<arg types>)_runtime`/`_deploy`, as
Python Vyper does, minus the function id). Each has an exact bytecode
comparison in `eval/evalCompilerInternalLabelsScript.sml`, included in the
default lowering rollup.

| Source | Internal name | Before |
|---|---|---|
| `p69_int_name_code_end` | `code_end` | outside the whitelist; jumped to the data-section header |
| `p87_int_name_revert` | `revert` | outside the whitelist; jumped to the shared revert stub |
| `p88_int_name_fn_prefix` | `fn_foo`, next to external `foo` | `compile_vyper = NONE` |
| `p90_int_name_fn_prefix_unused` | `fn_foo`, called from `bar`, next to external `foo` | `compile_vyper = NONE` |
| `p89_int_name_entry` | `__entry` | `compile_vyper = NONE` |
| `nm_int_entry` | `__entry`, no arguments | `compile_vyper = NONE` |
| `p70_int_name_reachable` | `reachable_f` | outside the whitelist; matched |
| `p71_int_name_return_label` | `return_label_f` | outside the whitelist; matched |

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), with the same settings and
commands as `../name-collisions/README.md`, run from `sources/`.
