# Memory-store differential results

Exact matches increased from 4 to 40 across 54 sources. The 13 remaining
bytecode differences and one compiler rejection are attributed to the linked
issues below.

The comparison covers the 51 distinct Vyper sources supplied in
[issue #549](https://github.com/verifereum/vyper-hol/issues/549) and
its source comment, plus three controls: long String/Bytes literals assigned to
larger bounds and a one-word storage aggregate. The one-word tuple member
`t11` is among the issue sources. All sources were accepted by the stock HOL
contract checker in deployment and runtime modes.

Baseline: `edfc59af7c630ca22f5be04b4becb208fb18a6fd` (#576). After core:
`6e722319`, including `99bdf83c`'s full-capacity list-allocation prerequisite
from #560 and the ABI-produced source-bound correction. All after results use
that core revision. Each side used its own worktree and the same generated inputs. `compile_vyper`
was evaluated with stock checker/EVAL libraries and
the existing finite-map compset and `fmap_to_alist_FEMPTY`, `i2w_pos` and
`set_byte_bit_field_insert` computation rules. There was no compiler evaluator
substitution. The diagnostic per-source bound
was 900 seconds; the proof-step timeout was unchanged.

The oracle is Vyper `0.5.0a4+cd74ce4f+commit.cd74ce4f`, pinned by `VYPER_PIN`,
with experimental codegen, no optimization, Prague and bytecode metadata disabled.
The retained 29 JSON/bytecode fixtures and dependency provenance reproduced
byte for byte with `prepare --check`. Diagnostic probes used holbuild 0.11.4;
CI proof builds used the repository-pinned holbuild 0.11.3. Tuple execution used
py-evm 0.12.1b1 (PragueVM) and eth-abi 6.0.0.

Since this comparison, `p16_return_tuple_bytes_widen` from #542 has been added
as a 30th retained fixture; its bytecode matches the oracle. The
`set_byte_bit_field_insert` rule is no longer needed: `word_of_bytes_T_0w_256` in
`vyperMiscScript.sml` lets EVAL compute 256-bit words built from bytes.

`MATCH` means both deployment and runtime bytes are identical. Difference cells
show HOL/Vyper runtime lengths and the first differing byte (zero-based).
`NONE` means the checker accepted but `compile_vyper` returned `NONE`.
Whitelist membership is recorded separately as baseline → after; it does not
control whether a witness is compiled.

| Source | Whitelist | Baseline | After | Remaining owner |
|---|---|---|---|---|
| `a01_str_local_reassign` | F → T | 310/390 B, rt@54 | MATCH (390 B) |  |
| `a02_bytes_local_from_arg` | F → T | 270/292 B, rt@54 | MATCH (292 B) |  |
| `a09_local_array_from_storage` | F → F | 199/197 B, rt@54 | MATCH (197 B) |  |
| `a10_local_struct_from_storage` | F → F | 156/152 B, rt@54 | MATCH (152 B) |  |
| `a11_local_string_from_intcall` | F → T | 332/412 B, rt@54 | MATCH (412 B) |  |
| `a12_local_dynarray_from_arg` | F → F | 159/146 B, rt@54 | MATCH (146 B) |  |
| `bytes_same_assign` | F → F | 228/270 B, rt@53 | MATCH (270 B) |  |
| `c01_ctrl_str_local_decl` | T → T | 252/293 B, rt@53 | MATCH (293 B) |  |
| `c03_annassign_empty_dynarray` | F → F | 166/149 B, rt@54 | MATCH (149 B) |  |
| `c04_annassign_empty_bytes` | F → F | 91/76 B, rt@54 | MATCH (76 B) |  |
| `c05_assign_empty_builtin_string` | F → F | 257/296 B, rt@53 | MATCH (296 B) |  |
| `c06_assign_empty_storage_dynarray` | F → F | 117/64 B, rt@54 | MATCH (64 B) |  |
| `c07_annassign_str_same_len` | T → T | 244/287 B, rt@53 | MATCH (287 B) |  |
| `c12_annassign_empty_bytes_ret` | T → T | 213/200 B, rt@54 | MATCH (200 B) |  |
| `concat_storage` | F → F | 327/349 B, rt@54 | 325/349 B, rt@54 | [#566](https://github.com/verifereum/vyper-hol/issues/566) |
| `dec_from_memory2` | T → T | 187/228 B, rt@54 | MATCH (228 B) |  |
| `e70_noData_live_mem2` | T → T | 280/323 B, rt@54 | MATCH (323 B) |  |
| `empty_bys_i8` | F → F | 172/187 B, rt@54 | 196/187 B, rt@54 | [#548](https://github.com/verifereum/vyper-hol/issues/548) |
| `empty_dynarr_local` | F → F | 254/253 B, rt@54 | 251/253 B, rt@54 | [#560](https://github.com/verifereum/vyper-hol/issues/560) |
| `enc_in_assign` | F → F | 228/272 B, rt@53 | MATCH (272 B) |  |
| `enc_multi_local` | F → F | 249/304 B, rt@53 | 288/304 B, rt@54 | [#551](https://github.com/verifereum/vyper-hol/issues/551) |
| `eq_string_storage` | F → F | 173/171 B, rt@54 | MATCH (171 B) |  |
| `ifexp_storage_string` | F → F | 316/317 B, rt@54 | 316/317 B, rt@54 | [#561](https://github.com/verifereum/vyper-hol/issues/561) |
| `long_bytes_literal` | T → T | 291/333 B, rt@54 | MATCH (333 B) |  |
| `long_string_literal` | T → T | 291/333 B, rt@54 | MATCH (333 B) |  |
| `p02_int_local_string` | F → F | 361/401 B, rt@54 | 401/401 B, rt@138 | [#545](https://github.com/verifereum/vyper-hol/issues/545) |
| `p06_local_append_struct` | F → F | 205/177 B, rt@54 | MATCH (177 B) |  |
| `p11_storage_append_struct` | F → F | 208/211 B, rt@54 | 208/211 B, rt@54 | [#560](https://github.com/verifereum/vyper-hol/issues/560) |
| `p13_local_append_struct_var` | F → F | 222/196 B, rt@54 | 195/196 B, rt@54 | [#558](https://github.com/verifereum/vyper-hol/issues/558) |
| `p15_local_append_bytes` | F → F | 238/262 B, rt@53 | MATCH (262 B) |  |
| `p58_int_bytes_local` | F → F | 408/468 B, rt@54 | 448/468 B, rt@54 | [#545](https://github.com/verifereum/vyper-hol/issues/545), [#566](https://github.com/verifereum/vyper-hol/issues/566) |
| `p64_string_annassign_call` | T → T | 358/400 B, rt@54 | MATCH (400 B) |  |
| `r01_assert_var_reason` | F → T | 356/396 B, rt@54 | MATCH (396 B) |  |
| `r02_assert_concat_reason` | F → F | 416/439 B, rt@54 | 416/439 B, rt@54 | [#566](https://github.com/verifereum/vyper-hol/issues/566) |
| `r03_raise_var_reason` | F → T | 356/396 B, rt@54 | MATCH (396 B) |  |
| `r04_raise_arg_reason` | F → T | MATCH (297 B) | MATCH (297 B) |  |
| `r07_assert_storage_string_reason` | F → F | 337/344 B, rt@54 | MATCH (344 B) |  |
| `r08_assert_ctrl_literal` | T → T | MATCH (337 B) | MATCH (337 B) |  |
| `r10_raise_uint2str_reason` | F → F | 389/396 B, rt@54 | 389/396 B, rt@54 | [#561](https://github.com/verifereum/vyper-hol/issues/561) |
| `r11_assert_long_literal_reason` | T → T | MATCH (376 B) | MATCH (376 B) |  |
| `rc07_rof_false_tuple` | F → F | NONE | NONE | [#554](https://github.com/verifereum/vyper-hol/issues/554) |
| `rc16_msgdata_tuple` | F → F | 248/370 B, rt@1 | 419/370 B, rt@57 | [#552](https://github.com/verifereum/vyper-hol/issues/552), [#554](https://github.com/verifereum/vyper-hol/issues/554) |
| `storage_one_word_array` | F → F | 142/104 B, rt@54 | MATCH (104 B) |  |
| `t01_tuple_assign_intcall` | F → F | 182/184 B, rt@54 | MATCH (184 B) |  |
| `t03_tuple_assign_abi_decode` | F → F | 196/198 B, rt@54 | MATCH (198 B) |  |
| `t04_tuple_assign_extcall` | F → F | 242/244 B, rt@54 | MATCH (244 B) |  |
| `t05_tuple_assign_storage_targets` | F → F | 126/128 B, rt@54 | MATCH (128 B) |  |
| `t06_tuple_assign_mixed_targets` | F → F | 234/236 B, rt@54 | MATCH (236 B) |  |
| `t07_tuple_assign_string_elems` | F → F | 216/437 B, rt@53 | MATCH (437 B) |  |
| `t08_tuple_assign_ret_type_mismatch` | F → F | 407/401 B, rt@54 | MATCH (401 B) |  |
| `t11_tuple_onew_decode_mem` | F → F | 262/266 B, rt@54 | MATCH (266 B) |  |
| `tup_unpack_local` | F → F | 165/167 B, rt@54 | MATCH (167 B) |  |
| `x08_return_storage_string` | F → F | MATCH (342 B) | MATCH (342 B) |  |
| `x09_ifexp_storage_string` | F → F | 316/317 B, rt@54 | 316/317 B, rt@54 | [#561](https://github.com/verifereum/vyper-hol/issues/561) |

The independent runtime checks reproduce the original defects and their fixes:

| Runtime | Baseline HOL | Pinned Vyper | After HOL |
|---|---|---|---|
| `t07.f()` | `Invalid opcode 0xfe @ 99` | `"ab"` | `"ab"` |
| `t08.f()` | `("x", 0)` | `("x", 3)` | `("x", 3)` |

To reproduce, generate the oracle with the pinned Python environment, then run
`probe` once in each prepared worktree. The script saves source-version hashes,
checker outcomes, whitelist results, closed EVAL results, bytecode and any residuals:

```sh
python lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --fixtures /tmp/memory-store-oracle --check
python3 lowering/defs/bytecode/memory_store_witnesses.py probe \
  --repo WORKTREE --fixtures /tmp/memory-store-oracle --output RESULT_DIRECTORY
python lowering/defs/bytecode/memory_store_witnesses.py execute \
  --fixtures /tmp/memory-store-oracle --output RESULT_DIRECTORY
```

These results establish the listed comparisons. Issue #549 also documents an
untested frontend limitation: empty `HexBytes` and `Bytes` literals share a
representation, although Vyper's empty-value fast path distinguishes them.
