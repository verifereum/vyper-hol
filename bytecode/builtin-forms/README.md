# Builtin form witnesses (#566)

Exact bytecode comparisons for `extract32`, `concat`, `slice` of a `bytes32`
or a `.code` source, and `ceil`, checked by
the native runner (`../native/README.md`); from `bytecode/`:

```sh
./native/bytecode_parity_native.exe . builtin-forms
```

`uint2str_local` is out of parity for now and is skipped by the runner; see
`../pending-uint2str-buffer.md`.
The sources whose bytes vyperlang/vyper#5127 changed at the v0.5.0b1 pin are
skipped too; [`pending-5127-port.md`](../pending-5127-port.md) names what
brings each back.

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
