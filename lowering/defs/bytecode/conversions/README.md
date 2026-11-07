# Conversion witnesses (#548)

`parity-fixtures.txt` names the 6 required bytecode fixtures. Each source in
`sources/` has independently generated annotated AST/layout JSON and deployment
and runtime bytecode in `oracle/`. `evalCompilerConversionsTheory` checks both
checker modes and proves each retained complete bytecode pair equal to the HOL compiler's
output, using the same `memoryStoreWitnessLib` as the other compiler witnesses.

`checker-sources/` and `checker-oracle/` retain the three codegen-rejected
literal controls, which the HOL checker accepts. `typecheck-rejected/` holds 12
controls that the pinned Vyper's type checker rejects (`_convert_rules.py`), so
their annotated AST/layout JSON comes from Vyper `9362e36b`, the last pin that
accepted them: the ten conversions outside Vyper's input sets or inconsistent in
width must fail the HOL checker, while the two conversions where HOL lowering
and source semantics agree are still accepted by it. The same theory checks
these verdicts on the exported ASTs in both modes.

The default CI builds the theory and reproduces both sets of independent inputs
with pinned Vyper, experimental codegen, Prague, `-O none`, and no metadata.
The parent `python-o1-bytecode-fixtures` script supplies the canonical compiler
environment and runs these generators:

```sh
python3 lowering/defs/bytecode/memory_store_witnesses.py prepare \
  --corpus conversions --repo . --fixtures /tmp/conversion-parity --check
python3 lowering/defs/bytecode/conversion_witnesses.py \
  --repo . --output /tmp/conversion-checker --check
holbuild -j4 build evalCompilerConversionsTheory conversionProofAuditTheory
```
