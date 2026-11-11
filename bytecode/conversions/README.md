# Conversion witnesses (#548)

`parity-fixtures.txt` names the 6 required bytecode fixtures. Each source in
`sources/` has independently generated annotated AST/layout JSON and deployment
and runtime bytecode in `oracle/`. The native runner checks that the HOL checker
accepts each source in both modes and that each complete bytecode pair equals
the HOL compiler's output (`../native/README.md`).

`checker-sources/` and `checker-oracle/` retain the three codegen-rejected
literal controls, which the HOL checker accepts. `typecheck-rejected/` holds 12
controls that the pinned Vyper's type checker rejects (`_convert_rules.py`), so
their annotated AST/layout JSON comes from Vyper `9362e36b`, the last pin that
accepted them: the ten conversions outside Vyper's input sets or inconsistent in
width must fail the HOL checker, while the two conversions where HOL lowering
and source semantics agree are still accepted by it. `compilerLoweringTestTheory`
(`tests/`) checks these verdicts on the exported ASTs in both modes.

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
