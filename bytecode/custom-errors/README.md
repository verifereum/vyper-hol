# Custom-error witnesses

These sources exercise the lowering of `raise E(...)` and `assert c, E(...)`
for a declared `error E` ([issue #1195](https://github.com/verifereum/vyper-hol/issues/1195)).
The HOL lowering snapshots the arguments in declaration order and encodes
them directly after the declared selector, following
`_revert_with_custom_error` in the pinned compiler. An error without
arguments reverts with the four-byte selector alone. Compare deployment
and runtime bytes with the pinned oracles by running
`./native/bytecode_parity_native.exe . custom-errors` from `bytecode/`.

| Source | Checks |
|---|---|
| `ce_raise_noargs` | `raise` of an error without arguments: the selector alone |
| `ce_assert_noargs` | the same on a failed `assert` |
| `ce_raise_static` | static arguments (`uint256`, `address`, `bytes32`), positional |
| `ce_assert_static` | static arguments on a failed `assert` |
| `ce_raise_kwargs` | keyword arguments, in declaration order |
| `ce_raise_dynamic` | a static argument followed by `String` and `Bytes` arguments |
| `ce_assert_dynamic` | a string literal with a wider declared `String` parameter type |
| `ce_raise_dynarray` | a `DynArray` argument |

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`, with `../patches/` applied), with
the provenance record of the compiler, its settings, dependencies and
input/output hashes. Reproduce it from the repository root:

```sh
python bytecode/memory_store_witnesses.py prepare \
  --corpus custom-errors --fixtures /tmp/custom-error-oracle --check
```
