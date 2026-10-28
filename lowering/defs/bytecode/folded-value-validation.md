# Folded-value validation

The frontend, checker regressions, seven parity proofs, 37 witness sources and
36 independently generated AST/bytecode pairs are permanent test inputs.
Raw logs, generated HOL exports, duplicate inputs and intermediate runner state
are retained in a separate evidence archive rather than in the source tree.

## Evidence archive

[folded-value-evidence.json](folded-value-evidence.json) records the archive's
SHA256, 737-file inventory count and source commit. The local copy is
`.agent-files/folded-value-evidence.tar.gz` (ignored by Git). It has not been
uploaded to an artifact service. While the original branch history is available,
the identical archive can be recovered from the recorded commit:

```sh
git archive --format=tar.gz --output=/tmp/folded-value-evidence.tar.gz \
  b4dccda4620d60e06a406fb48efea3cb16346426 \
  notes/validation/folded-value-2026-10-23 \
  notes/validation/folded-value-2026-10-24
python3 lowering/defs/bytecode/verify_folded_evidence.py \
  /tmp/folded-value-evidence.tar.gz
```

Preserve the archive as a PR/CI attachment before discarding or squashing the
original history. Its two directories contain the original reports, all
commands/logs, per-witness results, corpus outcomes, execution receipts, source
hashes and historical proof audits. The verifier reads the archive without
extracting it and checks its checksum, internal manifests, retained witness and
oracle identities, emitted bytes, compiler settings, four EVM receipts and
archived proof logs.

This verifies **historical evidence**, not a fresh run of a changed compiler.
The original independent run used source revision
`ac6681fe013c4762158d1bc24e9ae206a19781e8`. Subsequent merges from `main`
changed recorded sources and moved checker tests; the previous `verify_current.py`
already failed its freshness check before the archive reduction. The replacement
reports all changed/missing source and proof paths. Add `--require-current` to
make any such drift fail; do not treat historical results as current validation.

## Recorded independent results

Pinned Vyper: 0.5.0a4 commit `cd74ce4f` (full revision in `VYPER_PIN`).
Toolchain: uv 0.10.11, CPython 3.11.11; experimental codegen, optimize NONE
(Venom O1), Prague, no bytecode metadata. Full provenance accompanies the
retained oracle inputs in `folded-value-oracle/provenance.json`.

| Historical outcome | Witnesses |
|---|---|
| Deploy and runtime bytes match Python | 30 |
| Expected Python rejection (`method_id_var`) | 1 |
| ABI bytecode mismatches | 4 |
| Immutable compilation returns NONE | 2 |

All 36 accepted ASTs passed both checker modes. Both producers' runtime
bytecodes reverted for `pow_folded_exp.f(2**90)` and
`pow_negfold_base.f(256)`: four py-evm 0.12.1b1 PragueVM execution receipts.

The ABI mismatches were `ctl03_abi_method_id` and `enc_ensT_uint_mid` (#551),
`rc09_abi_encode_data` (#554/#551), and `rr03_abi` (#567/#551). The immutable
NONEs were `i12_immut_with_storage` and `p29_imm_multi` (#563).
Python's 101-fixture corpus and memory-store/external-call subcorpora reproduced.
Of 33 attempted HOL corpus targets, 28 passed and five had resource/build
failures. These are recorded failures, not passing tests or a green full corpus.

## Current HOL checks

Run the retained parity and regression checks from the repository root:

```sh
holbuild -j4 --maxheap 12000 build \
  foldedValueParityTheory foldedValueValidationPrepTheory \
  vyperTupleSubscriptTestTheory vyperRawCallCalldataTestTheory \
  vyperTypeBuiltinsTheory supportedExprFormPropsTheory
```

These focused checks passed on 2026-10-26 after removing the evidence bundles;
all seven public parity proofs and their staged theorem audits passed.

The broader current build was also attempted, including
`vyperTypeContractSoundnessTheory` and `vyperLoweringCorrectTheory`. The manifest
preloads the toolchain context for dependent `intLib` users to resolve legacy
load-order errors. The broader build then stops at an unchanged proof:
`eval_ext_call_no_control` in `vyperExprNoControlTheory` times out at both 2.5 and
10 seconds in `gvs[AllCaseEqs(), no_control_exc_def]`. The reduction preserves
all proofs and tests; no proof statements or default tactic budgets changed.

After resolving that independent blocker, build those two broader targets and
run the preserved full theorem audit:

```sh
holbuild -j4 --maxheap 12000 build \
  vyperTypeContractSoundnessTheory vyperLoweringCorrectTheory
holbuild --maxheap 12000 run lowering/defs/bytecode/folded-value-audit.sml
```

For a forced rebuild of the ten staged parity theories without checkpoint or
proof-step reuse:

```sh
holbuild -j4 --maxheap 12000 build --force=theory \
  --skip-checkpoints --skip-proof-steps \
  foldedValueParityTheory foldedValueParityComputeTheory \
  foldedValueParityAbiComputeTheory foldedValueParityAbiInputTheory \
  foldedValueParityAbiPipelineTheory foldedValueParityAbiReadyTheory \
  foldedValueParityAbiTheory foldedValueParityAddTheory \
  foldedValueParityPowTheory foldedValueParityConstantsTheory
```

The audit checks empty hypotheses and absence of non-DISK_THM oracle tags for
all staged parity, frontend/checker, type-soundness and supported-form theorems.
It reconstructs each of the seven public parity statements independently from
the retained AST and oracle files. Expected bytes remain ordinary test data.

Three pre-existing lowering admissions remain outside this issue's scope:
`lower_vyper_runtime_unit_correct`,
`lower_vyper_runtime_unit_source_unit_ok`, and
`lower_vyper_runtime_unit_memory_ok`. The audit prints their tags separately;
neither the historical reports nor these checks certify globally cheat-free
lowering correctness. Supported-program restrictions remain in place.

## Reproducing the external run

Use `folded-value-witnesses.txt` as the complete inventory and
`folded-value-parity-fixtures.txt` for the seven permanent parity cases.
Provision the pinned Vyper checkout and isolated Python environment using the
procedure in `python-o1-bytecode-fixtures`. Generate expected bytes with
`python_o1_bytecode_oracle.py`, export `annotated_ast,layout`, and sanitize with
`tests/sanitize_check_contract_json.py`; accepted ASTs and expected bytes must
come from the same pinned installation and exact witness sources.

Check each accepted AST in both deployment modes, evaluate
`compile_vyper (K SOME) (o1_policy all_capabilities) tops`, and compare both
byte arrays. Record supported_program separately from byte equality.
Capture the actual Python rejection for `method_id_var`, rerun the full corpus
with `python-o1-bytecode-fixtures --compare-hol`, and execute both overflow
cases on both producers' runtime bytecodes. Preserve source/artifact hashes,
commands, exit statuses and dependency-owned failures. The archive's `runner/`
directory retains the original harnesses and detailed reproduction procedure.
