# Current folded-value proof verification (2026-10-24)

## Result

Alan's L0006/G0007 tactic-budget blocker is no longer applicable to the current
split proof sources. All seven ordinary parity theorem declarations now build
from scratch, with checkpoints and proof-step reuse disabled and the default
tactic budget unchanged. Their public statements explicitly compare the actual
frontend input with the independent Python oracle; they no longer interpolate
the supporting theorem's conclusion.

`verification.json` identifies all current proof sources and retained logs by
SHA256. `audit.sml` checks every staged parity theorem, frontend/checker test,
builtin/contract type-soundness theorem, and supported-expression theorem for
empty hypotheses and absence of non-DISK_THM oracle tags. It also reconstructs
and compares all seven public statements against independently loaded AST and
oracle files. The audit passes. No expected-byte equality is installed as an
evaluator rule; no compiler definition or whitelist restriction was changed.

## Commands and receipts

Run from the repository root; each command exited zero:

```sh
holbuild -j4 --maxheap 12000 build --force=theory --skip-checkpoints --skip-proof-steps \
  foldedValueParityTheory foldedValueParityComputeTheory \
  foldedValueParityAbiComputeTheory foldedValueParityAbiInputTheory \
  foldedValueParityAbiPipelineTheory foldedValueParityAbiReadyTheory \
  foldedValueParityAbiTheory foldedValueParityAddTheory \
  foldedValueParityPowTheory foldedValueParityConstantsTheory
holbuild -j4 --maxheap 12000 build --force=theory \
  foldedValueValidationPrepTheory vyperCheckContractFrontendLibTestTheory \
  vyperCheckContractLibTestTheory jsonConstEvalWitnessTheory \
  vyperTupleSubscriptTestTheory vyperRawCallCalldataTestTheory
holbuild -j4 --maxheap 12000 build --force=theory \
  vyperTypeBuiltinsTheory vyperTypeContractSoundnessTheory
holbuild -j4 --maxheap 12000 build --force=theory --skip-checkpoints --skip-proof-steps \
  supportedExprFormPropsTheory
holbuild -j4 --maxheap 12000 build --force=theory vyperLoweringCorrectTheory
holbuild --maxheap 12000 run notes/validation/folded-value-2026-10-24/audit.sml
python3 notes/validation/folded-value-2026-10-24/verify_current.py
```

Logs are in `logs/`. Individual parity theory build logs are retained as well
as command summaries. The complete parity rebuild took 324 seconds across ten
theories; this is not a claim that the entire compiler evaluates in 30 seconds.
The cache-output warning in that run concerns regenerated serialized artifacts;
the proof/tag audit independently checks the resulting theorems.

The first supported-expression rebuild encountered a toolchain preload-order
error: `intLib` reached `hurdUtils.sml` before `hurdUtilsContextTheory` existed in
the ML environment. The manifest now explicitly preloads that context for this
action. The unchanged proof subsequently builds with checkpoints disabled.
No toolchain files or proof statements were modified to work around the error.

## Reconciliation with independent evidence

The original `../folded-value-2026-10-23/` bundle is preserved unchanged; its old
parity-script hash is historical, not certification of this refactor.
`verify_current.py` verifies all 714 historical bundle files, 572 unchanged
semantic/source files (the remaining inventory entry is the updated validation
Markdown, explicitly recorded as documentation-only), all 37 witness identities,
accepted AST/oracle identities,
actual emitted byte arrays, pinned compiler settings, and four genuine overflow
reverts. This source identity check justifies reusing the external run: frontend,
checker, lowering semantics and the witnesses have not changed.

The retained independent results remain **30 MATCH, one expected Python
rejection, four ABI mismatches, two immutable compile-NONEs**. All task-owned
operator, builtin, MethodId and ABI-keyword witnesses MATCH. Both producers
revert for `pow_folded_exp.f(2**90)` and `pow_negfold_base.f(256)`.

The full existing corpus was rerun: Python's 101 fixtures and the two subcorpora
reproduced; all 33 HOL targets were attempted, 28 passed and five were unsuccessful.
The latter are resource/build failures, not proven baseline semantic defects or
passing tests. No claim of a green full corpus is made. Exact outcomes remain in
the original report and corpus logs.

The #551 controls still mismatch because `ensure_tuple` is unused by the current
ABI lowering. #554/#567 retain the nested ABI failures; #563 retains the immutable
NONEs. These are the TASK's expressly dependency-owned validation cases, not
newly concealed successes. Exp, MethodId and ABI whitelist restrictions remain.

## Out-of-scope baseline admissions (owner clarification)

The rebuilt `vyperLoweringCorrectTheory` **still reports three pre-existing
CHEATs**, which this change neither introduces nor removes:

- `lower_vyper_runtime_unit_correct`
- `lower_vyper_runtime_unit_source_unit_ok`
- `lower_vyper_runtime_unit_memory_ok`

Their theorem tags are explicitly printed by the audit, and their native build
log is retained. The owner subsequently confirmed that pre-existing cheats not
explicitly part of this task need not be proved. These compiler-wide milestone
admissions are therefore outside this task's acceptance scope, not blockers.
The task-specific frontend/checker, type-soundness and seven fixture proofs are
verified without cheats; global cheat-free lowering certification must not be
inferred. The task is complete under that clarified scope. Separately owned
validation dependencies and unsuccessful corpus runs remain reported above.
