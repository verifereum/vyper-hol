# Opt-in source-module parity

This is a separate test entry point. Neither `sourceModule` implementation nor
ordinary public frontend APIs are changed by these tests.

## Contract

- `sourceModuleParityInputTheory`: all 37 retained **whole source** programs;
  all 36 pin-valid cases must elaborate and pass `check_contract T`. The only
  pin-invalid case is `method_id_var`. Constructors are not skipped.
- `sourceModuleParityTheory`: nine deploy/runtime byte-pair equations (the
  seven retained cases plus `fold_not` and `boolop_and3`) through
  `source_module_compile`, plus exact phase/check/compiler composition. The
  backend input must be exactly the modules checked above. Oracle byte arrays
  are test data, never computation rewrite rules.
- `sourceModuleParityProbe.sml`: broader 37-row compiler probe, with concrete
  wrapper outputs, kernel-tag receipts and supported-program observations.
  Backend NONE, byte mismatches and resource failures are not acceptance. The ML
  probe completes the inventory diagnostically; `summarize` is the fail-closed
  overall result and exits nonzero if any pin-valid row fails parity.
- `sourceModuleParityAudit.sml`: reopens exported theory objects and reconstructs
  their source inputs and expected pinned bytes; rejects hypotheses, axioms and
  every oracle tag other than the normal `DISK_THM` storage marker.

## Independent pin and receipts

Run from the repository root. The prepared isolated environments reside under
`.agent-files/folded-value-validation`; no historical outputs are used as fresh
execution receipts.

```sh
python3 tests/sourceModuleParity.py oracle
.agent-files/.holbuild-toolchain/bin/holbuild sourceModuleParityTheory \
  --tactic-timeout 2.5 --allow-cache-timeout-discrepancy
# Refresh this diagnostic-only dependency too; `run` does not build it.
.agent-files/.holbuild-toolchain/bin/holbuild supportedProgramTheory \
  --tactic-timeout 2.5 --allow-cache-timeout-discrepancy
.agent-files/.holbuild-toolchain/bin/holbuild --maxheap 10000 \
  run tests/sourceModuleParityProbe.sml
.agent-files/folded-value-validation/evm-venv/bin/python \
  tests/sourceModuleParity.py execute
.agent-files/.holbuild-toolchain/bin/holbuild \
  run tests/sourceModuleParityAudit.sml
.agent-files/.holbuild-toolchain/bin/holbuild export \
  -o .agent-files/source-module-parity/source-module-parity.holbuild-export \
  sourceModuleParityTheory sourceModuleParityInputTheory
python3 tests/sourceModuleParity.py summarize   # nonzero on any source-matrix failure
python3 tests/sourceModuleParity.py snapshot

# Optional broader 101-fixture validation, not the 37-source result:
PATH=".agent-files/folded-value-validation/bootstrap/bin:$PATH" \
  lowering/defs/bytecode/python-o1-bytecode-fixtures --check \
  --vyper-repo .agent-files/folded-value-validation/vyper-src
python3 tests/sourceModuleParity.py corpus
```

`oracle` invokes the existing independent generator once per original witness,
including the negative witness. It asserts `VYPER_PIN`, CPython 3.11.11, the
isolated installation root, experimental codegen, optimize NONE (Venom O1),
Prague and no bytecode metadata. Both byte arrays must reproduce the retained
expected files. Expected bytes are never updated from HOL output. The separate
pre-erasure syntax check uses CPython 3.12 (the fixture generator's Python AST
shape includes `type_params=[]`) and the same pinned parser checkout.

Evidence lives in `.agent-files/source-module-parity/`: `single/*/generated/`
contains fresh independent expected bytes and full settings/package provenance;
`commands/*.json` records argv, exit, elapsed time and log SHA256; source manifests
hash untracked source-module files as well as tracked compiler/semantic files.
`hol/` contains actual wrapper conclusions, emitted bytes and audit receipts.
`executions.json` contains four fresh PragueVM executions: both producers for
`pow_folded_exp.f(2**90)` and `pow_negfold_base.f(256)`. Only genuine `Revert`
counts, not an arbitrary EVM exception.

See `docs/SOURCE_MODULE_PARITY_RESULTS.md` for current outcomes and failure owners.
The pin is authoritative; no rejection of a pin-valid program is excused as a
passing test, and no global source semantic-equivalence claim is made here.
