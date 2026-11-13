# Custom-error witnesses

These sources exercise the lowering of `raise E(...)` and `assert c, E(...)`
for a declared `error E` ([issue #1195](https://github.com/verifereum/vyper-hol/issues/1195)).
The HOL lowering follows Python Vyper before vyperlang/vyper#5127: it
stores the arguments in a tuple buffer at their declared types, ABI-encodes
them behind the error's selector and reverts with
`selector || abi_encode(args)`; an error without arguments reverts with the
selector alone. At `VYPER_PIN`, `_revert_with_custom_error`
(`codegen_venom/stmt.py`) lowers the arguments as values and encodes them
with the direct encoder, so every fixture here waits for that port (P4 in
[`../pending-5127-port.md`](../pending-5127-port.md)). Once it lands, each
source has an exact bytecode comparison, run by
`./native/bytecode_parity_native.exe . custom-errors` from `bytecode/`
(`../native/README.md`).

| Source | Checks |
|---|---|
| `ce_raise_noargs` | `raise` of an error without arguments: the selector alone |
| `ce_assert_noargs` | the same on a failed `assert` |
| `ce_raise_static` | static arguments (`uint256`, `address`, `bytes32`), positional |
| `ce_assert_static` | static arguments on a failed `assert` |
| `ce_raise_kwargs` | keyword arguments, in declaration order |
| `ce_raise_dynamic` | a static argument followed by `String` and `Bytes` arguments |
| `ce_assert_dynamic` | a string literal stored at a wider declared `String` type |
| `ce_raise_dynarray` | a `DynArray` argument |

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`, with `../patches/` applied), with
the provenance record of the compiler, its settings, dependencies and
input/output hashes. Reproduce it from the repository root:

```sh
python bytecode/memory_store_witnesses.py prepare \
  --corpus custom-errors --fixtures /tmp/custom-error-oracle --check
```
