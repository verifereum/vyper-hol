# Source-module parity regressions

This opt-in suite compares source-derived backend inputs with independently
pinned compiler output. It is separate from the
[ordinary frontend regressions](sourceOrdinaryAcceptance.md), not a general
source semantic-equivalence claim.

## Regression purpose

- `sourceModuleParityInputTheory` checks whole source programs, including
  constructors. Pin-valid inputs must elaborate and pass `check_contract T`;
  `method_id_var` is the pinned rejection case.
- `sourceModuleParityTheory` checks nine deploy/runtime byte-pair equations
  through `source_module_compile`, including `fold_not` and `boolop_and3`, plus
  exact phase/check/compiler composition. Backend inputs must be exactly the
  checked modules. Oracle bytes are test data, never computation rewrite rules.
- `sourceModuleParityProbe.sml` probes the broader source inventory. Backend
  `NONE`, byte mismatches and resource failures are not acceptance; `summarize`
  exits nonzero if any pin-valid row fails parity.
- `sourceModuleParityAudit.sml` reopens exported theory objects, reconstructs
  inputs and expected bytes, and rejects hypotheses, axioms and oracle tags
  other than the normal `DISK_THM` storage marker.

## Provenance and reproduction

Run from the repository root with isolated environments under
`.agent-files/folded-value-validation`:

```sh
python3 tests/sourceModuleParity.py oracle
holbuild sourceModuleParityTheory --tactic-timeout 2.5
# The diagnostic probe also needs this dependency; `run` does not build it.
holbuild supportedProgramTheory --tactic-timeout 2.5
holbuild --maxheap 10000 run tests/sourceModuleParityProbe.sml
.agent-files/folded-value-validation/evm-venv/bin/python \
  tests/sourceModuleParity.py execute
holbuild run tests/sourceModuleParityAudit.sml
holbuild export \
  -o .agent-files/source-module-parity/source-module-parity.holbuild-export \
  sourceModuleParityTheory sourceModuleParityInputTheory
python3 tests/sourceModuleParity.py summarize
python3 tests/sourceModuleParity.py snapshot
```

`oracle` invokes the independent generator on each original witness, including
the negative case. It enforces `VYPER_PIN`, CPython 3.11.11, the isolated
installation root, experimental codegen, optimize NONE (Venom O1), Prague and
no bytecode metadata. Both byte arrays must reproduce the retained expected
files; never update them from HOL output. The separate pre-erasure syntax check
uses CPython 3.12 for its Python AST shape and the same pinned parser checkout.

Generated evidence lives in `.agent-files/source-module-parity/` and includes
independent expected bytes, package/settings provenance, source hashes, wrapper
conclusions and audit output. `execute` runs both producers' runtime bytecodes
for `pow_folded_exp.f(2**90)` and `pow_negfold_base.f(256)` on PragueVM. Only a
genuine `Revert` counts, not an arbitrary EVM exception. Historical outputs are
not fresh execution evidence.

The broader bytecode corpus is a separate check:

```sh
PATH=".agent-files/folded-value-validation/bootstrap/bin:$PATH" \
  lowering/defs/bytecode/python-o1-bytecode-fixtures --check \
  --vyper-repo .agent-files/folded-value-validation/vyper-src
python3 tests/sourceModuleParity.py corpus
```
