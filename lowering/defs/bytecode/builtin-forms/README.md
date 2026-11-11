# Builtin form witnesses (#566)

Exact bytecode comparisons for `extract32`, `concat`, `slice` of a `bytes32`
or a `.code` source, and `ceil`, checked in
`eval/evalCompilerBuiltinForms{1,2,3,4}Script.sml` (rolled up by
`eval/evalCompilerBuiltinFormsScript.sml`, part of the default lowering
witnesses).
The other sources in this directory left the comparison at the v0.5.0b1 pin,
where vyperlang/vyper#5127 changed their bytes;
[`pending-5127-port.md`](../pending-5127-port.md) names what brings each back.

| Source | Checks |
|---|---|
| `extract32_default` | `extract32(b, i)`: the source's length and data pointer read before `start`, the bounds check `end < start or end > len`, the 32-byte load |
| `extract32_uint` | `output_type=uint256`: no clamp |
| `extract32_bytes4` | `output_type=bytes4`: `assert iszero(shl(32, val))` |
| `extract32_int128` | `output_type=int128`: the signed `slt`/`sgt` clamp |
| `extract32_addr` | `output_type=address`: `assert iszero(gt(val, 2**160 - 1))` |
| `ceil_dec` | `ceil(x)`: `slt(x, 0)` selects `x` or `x + 10**10 - 1` |
| `floor_dec` | control: `floor(x)` |
| `len_bytes_arg` | control: `len` of a `Bytes` argument |
| `slice_bytes32` | `slice` of a `bytes32`: a 32-byte scratch and the literal length 32 |
| `concat_bytes2` | `concat` of two `Bytes`: the running offset in a 64-byte memory temporary |
| `concat_bytesn` | `concat` of `bytes32`, `bytes4` and `Bytes` |
| `concat_one_bytes_arg` | `concat` of `Bytes` and `bytes4` |
| `concat_string3args` | `concat` of three `String`s |
| `concat_string3` | `concat` of `String`s around a literal |
| `len_concat` | `len(concat(a, b))` |
| `uint2str_local` | `concat("n=", uint2str(x))` |
| `concat_storage` | `concat` with a storage `Bytes` argument |
| `self_code_slice` | `slice(self.code, 0, 10)`: `CODESIZE`/`CODECOPY` |
| `ext_code_slice` | `slice(a.code, s, 10)`: the non-literal start, then the address, `EXTCODESIZE` and the bounds check before the output buffer, then `EXTCODECOPY` |
| `struct_code_slice` | a struct member named `code` is an ordinary memory slice |
| `struct_data_slice` | control: the same with a member named `data` |
| `p94_rbuf_bytes_ret_concat_arg` | internal call with a `concat` argument, `Bytes` return |
| `p97_rbuf_stack_tuple_ret_concat_arg` | the same, stack tuple return |
| `p98_rbuf_mem_tuple_ret_concat_arg` | the same, memory tuple return |
| `p99_rbuf_string_ret_concat_arg` | the same, `String` return |
| `p102_rbuf_bytes_ret_word_arg` | `concat` of two `bytes32` in the callee |
| `p103_rbuf_control_word_ret_concat_arg` | internal call with a `concat` argument, word return |
| `p58_int_bytes_local` | `concat` into a local in the callee |

`supported_builtin_form` does not yet admit `Concat`, `Slice`, `Ceil` or
`Acc Code`, nor `supported_type_builtin_form` `Extract32`, so these programs
are outside `supported_program`; their fixtures pin the lowering ahead of
that relaxation.

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`), produced as in
`../name-collisions/README.md`.
