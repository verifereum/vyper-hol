# Upstream-fix witnesses

Programs whose pinned-compiler bytes depend on an upstream Vyper fix that the
HOL lowering follows and that `../patches/` backports. Each matches the
patched pin exactly and differs from the pin without that patch, so a patch
dropped from the series or a lowering that stops following the fix fails
here. Run with `./native/bytecode_parity_native.exe . upstream-fixes` from
`bytecode/` (`../native/README.md`).

| Source | Patch | Checks |
|---|---|---|
| `uf5236_ifexp_nested_narrow` | `5236-ternary-arm-widening` | a ternary arm, an internal call returning a nested `DynArray` with a narrower inner bound, is copied into the result type's layout |
| `uf5256_tuple_widen_bytes` | `5256-tuple-widening-layout` | assigning `(Bytes[2], uint256)` to a `(Bytes[64], uint256)` local copies member-wise |
| `uf5298_int_to_decimal_bound` | `5298-int-decimal-clamp` | `convert(int256, decimal)` clamps with the lower bound rounded toward zero |
| `uf5331_ifexp_narrow_string` | `5331-ternary-arm-buffer` | a narrower bytestring arm is copied into a result-sized buffer |

`oracle/` holds the annotated AST/layout JSON and deployment/runtime bytecode
from the pinned Python Vyper (`VYPER_PIN`) with every patch in `../patches/`
applied (`../python-o1-bytecode-fixtures --install DIR`), with `vyper` from
that environment first on `PATH`:

```sh
python bytecode/memory_store_witnesses.py prepare \
  --corpus upstream-fixes --fixtures bytecode/upstream-fixes/oracle
```
