# Slice buffer witnesses (#561, a07-06)

Exact bytecode comparisons for `slice`, checked in
`eval/evalCompilerSliceBuffersScript.sml` (part of the default lowering
rollup). The lowering sizes slice output buffers as Python's
`new_temporary_value(out_t)` (`32 + ceil32(maxlen)`) and allocates the
`msg.data`/`.code` output buffer before the size opcode and bounds check.

| Source | Checks |
|---|---|
| `slice_msg_data` | `slice(msg.data, 0, 4)` (`CalldataSlice`): buffer size and allocation order |
| `slice_msg_data_var` | `slice(msg.data, s, 8)`: same, with a variable start |
| `slice_bytes_var` | control: memory `Bytes` source with variable start and length |
| `slice_storage_bytes` | control: storage `Bytes` source |
| `slice_string_lit` | control: `String` source with literal start and length |

`supported_builtin_form` admits `CalldataSlice` but not yet `Slice`, so the
general-slice programs are outside `supported_program`; their fixtures pin the
lowering ahead of that relaxation.

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), produced as in
`../name-collisions/README.md`.
