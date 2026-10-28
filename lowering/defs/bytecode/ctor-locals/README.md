# Constructor-local witnesses

Each source declares locals in its `__init__` body. Python Vyper gives every
local its own `alloca` (`Context.new_variable` in `codegen_venom/context.py`),
in the constructor as in any other body. The HOL lowering used to keep the
constructor's locals at fixed `MemLoc` addresses that `build_compile_env`
reserved after the arguments, starting at address 0 for a constructor without
arguments, so every deployment bytecode here differed from Python's. In
`ctor_local_across_call` the fixed slot was also invisible to alloca
liveness while the local stays live after the call. Each now has
an exact bytecode comparison in `eval/evalCompilerCtorLocalsScript.sml`,
included in the default lowering rollup.

| Source | Constructor |
|---|---|
| `ctor_local_word` | no arguments, two word locals |
| `ctor_arg_local_array` | one argument, a two-word array local |
| `ctor_local_across_call` | a word local live across an internal call whose callee has its own local |
| `ctor_for_range` | a word accumulator and a `range` loop variable |
| `ctor_arg_ifelse_local` | a local computed from an argument, read in both branches of an if/else |

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), with the same settings and
commands as `../name-collisions/README.md`, run from `sources/`.
