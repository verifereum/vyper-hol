# Conversion witnesses (#548)

`parity-fixtures.txt` names the 13 required bytecode fixtures. Each source in
`sources/` has independently generated annotated AST/layout JSON and deployment
and runtime bytecode in `oracle/`. `evalCompilerConversionsTheory` checks both
checker modes and proves each complete bytecode pair equal to the HOL compiler's
output, using the same `memoryStoreWitnessLib` as the other compiler witnesses.

`checker-sources/` and `checker-oracle/` retain the 15 codegen-rejected controls:
the seven inconsistent width conversions must fail the HOL checker, while the
eight conversions where HOL lowering and source semantics agree stay accepted.
The same theory checks these verdicts on the exported ASTs in both modes.

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
