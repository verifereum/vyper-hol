# Conversion witnesses (#548)

`parity-fixtures.txt` names the 13 required bytecode fixtures. Each source in
`sources/` has independently generated annotated AST/layout JSON and deployment
and runtime bytecode in `oracle/`. The native runner checks that the HOL checker
accepts each source in both modes and that each complete bytecode pair equals
the HOL compiler's output (`../native/README.md`).

`checker-sources/` and `checker-oracle/` retain the 15 codegen-rejected controls:
the ten conversions outside Vyper's input sets or inconsistent in width must
fail the HOL checker, while the five conversions where HOL lowering and source
semantics agree stay accepted.
`compilerLoweringTestTheory` (`tests/`) checks these verdicts in both modes.

CI reproduces both sets of independent inputs
with pinned Vyper, experimental codegen, Prague, `-O none`, and no metadata.
The parent `python-o1-bytecode-fixtures` script supplies the canonical compiler
environment and runs these generators:

```sh
python3 bytecode/memory_store_witnesses.py prepare \
  --corpus conversions --repo . --fixtures /tmp/conversion-parity --check
python3 bytecode/conversion_witnesses.py \
  --repo . --output /tmp/conversion-checker --check
```

Then check bytecode parity with the native runner, from `bytecode/`:

```sh
./native/bytecode_parity_native.exe . conversions
```
