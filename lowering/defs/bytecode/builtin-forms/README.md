# Builtin form witnesses (#566)

Exact bytecode comparisons for `ceil` and `floor`, checked in
`eval/evalCompilerBuiltinForms1Script.sml` (rolled up by
`eval/evalCompilerBuiltinFormsScript.sml`, part of the default lowering
witnesses).
The other sources in this directory left the comparison at the v0.5.0b1 pin,
where vyperlang/vyper#5127 changed their bytes;
[`pending-5127-port.md`](../pending-5127-port.md) names what brings each back.

| Source | Checks |
|---|---|
| `ceil_dec` | `ceil(x)`: `slt(x, 0)` selects `x` or `x + 10**10 - 1` |
| `floor_dec` | control: `floor(x)` |

`supported_builtin_form` does not yet admit `Concat`, `Slice`, `Ceil` or
`Acc Code`, nor `supported_type_builtin_form` `Extract32`, so these programs
are outside `supported_program`; their fixtures pin the lowering ahead of
that relaxation.

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), produced as in
`../name-collisions/README.md`.
