# For-over-array witnesses (#559)

Each source iterates over an array. The lowering of `For x in <array>`
takes the iterable's shape (DynArray or fixed), its length or capacity and
its element type from the iterable's type, and its location from the
iterable's compiled value. It checks a DynArray's length against its
capacity in the loop's entry block, allocates the loop variable after the
iterable and its length, and copies a storage or transient element with
the slot word-copy loop, a single slot included. This is what Python's
`_lower_iter_loop` (`vyper/codegen_venom/stmt.py`) does at `VYPER_PIN`.
Each source has an exact bytecode comparison, run by
`./native/bytecode_parity_native.exe . for-iterables` from `bytecode/`
(`../native/README.md`).

| Source | Iterable | Before: HOL / Vyper runtime bytes |
|---|---|---|
| `f05_for_literal_list` | `[1, 2, 3]` | 177 / 161 |
| `f20_for_list_of_vars` | `[a, b, a]` | 207 / 191 |
| `f50_for_subscript_row` | `rows[0]` of a 2-D local | 263 / 247 |
| `f38_for_storage_struct_field_arr_set` | `self.st.arr`, a storage struct's field (also in `../nested-places`) | 285 / 322 |
| `f03_for_storage_dynarray` | storage `DynArray[uint256, 5]` | 270 / 321 |
| `f04_for_storage_fixed` | storage `uint256[3]` | 245 / 287 |
| `g8_a_iter_transient` | transient `uint256[2]` | 215 / 257 |
| `f24_for_local_dynarray` | memory local `DynArray` | matched |
| `f01_for_calldata_dynarray` | `DynArray` argument | matched |
| `g8_a_iter_struct_elem` | storage array of two-slot structs | matched |
| `f23_for_local_fixed` | memory local `uint256[3]` | matched |
| `f06_for_calldata_fixed` | `uint256[3]` argument | matched |

With the change all twelve match. The DynArray length check moved to where
Python puts it; in `f01` and `f24` the bytecode was the same either way.

`oracle/` holds the annotated AST/layout JSON and deployment/runtime
bytecode from the pinned Python Vyper, made from the repository root with
that Vyper on `PATH`:

```sh
python3 bytecode/memory_store_witnesses.py prepare \
  --corpus for-iterables --repo . \
  --fixtures bytecode/for-iterables/oracle
```
