# Slice buffer witnesses (#561, a07-06)

Exact bytecode comparison for `slice` of a storage `Bytes` source, checked in
`eval/evalCompilerSliceBuffersScript.sml` (part of the default lowering
rollup). The comparisons of the other sources left the checks at the v0.5.0b1
pin, where the Python bytes changed, and return when the change is ported
([`pending-5127-port.md`](../pending-5127-port.md)). The lowering sizes slice output buffers as Python's
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
