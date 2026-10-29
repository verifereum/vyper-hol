# PHI-merged memory pointer witnesses (#561)

Exact bytecode comparisons for programs whose result is a PHI of memory
pointers, checked in `eval/evalCompilerPhiPointers1Script.sml` and
`eval/evalCompilerPhiPointers2Script.sml` (part of the default lowering
rollup). The base-pointer analysis keeps the allocation behind
such a PHI live (a14-01), MakeSSA orders the PHIs of one block as Python does
(a14-02), `uint2str` sizes its buffer as Python does (a07-06), and a non-word
ternary is a memory pointer value (a10-04).

| Source | Checks |
|---|---|
| `uint2str_arg` | `uint2str(x)`: the digit buffer is reached only through the result PHI |
| `ifexp_string` | `String` ternary returned directly |
| `ifexp_bytes` | `Bytes` ternary with a literal branch |
| `ifexp_dynarray` | `DynArray` ternary |
| `ifexp_sarray` | static-array ternary assigned to a local, copied through a temporary |
| `ifexp_struct` | struct ternary assigned to a local, copied through a temporary |
| `ifexp_bytes20`, `ifexp_flag`, `ifexp_decimal` | control: word ternaries stay stack values |
| `ctl_sarray_assign` | control: static-array local from a parameter, no ternary |
| `ctl_ret_string_phi` | control: `String` result chosen by `if`/`else` statements |

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), produced as in
`../name-collisions/README.md`.
