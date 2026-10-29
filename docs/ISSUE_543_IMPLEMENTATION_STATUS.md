# #543: scoped implementation and verification

Baseline: `2fb2f375f6a001b7a6ba3ccc8c8ba87538768512`.
Authority: Vyper `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`.
This report covers #543, not full #135 frontend completeness, unrestricted
compiler correctness, or completion of neighboring backend issues.

## Delivered

- Original expressions, qualifiers, annotations, defaults and identities survive
  pre-erasure loading. Compiler folded fields are discarded before ordinary
  claim decoding. Mismatched syntax and invalid present claims fail explicitly.
- The common HOL source evaluator computes #543 constants and required bounds,
  tuple indices, ABI flags/selectors and standalone `method_id`. Mathematical
  source arithmetic is distinguished from bounded runtime arithmetic.
- Clean ordinary `prepare_check_input` / `check_contract*` APIs use the paired
  `sourceOrdinaryProgramLib` bridge. Runtime residual forms retain explicit
  legacy type/import/layout claims; they are not subjected to incomplete full
  Source inference. Residual mode is selected before evaluation, never as a
  retry after Source failure. Annotated-only APIs are explicitly `*_legacy`.
- The strict constant-file API uses the same source evaluator, without fallback.
  The original program, pairing, phase, linking and genuine deployment checker
  equations accompany the normalized modules. Compilation uses exactly those
  checked modules.
- All **36 valid retained programs** pass; `method_id_var` rejects. All **26
  existing ordinary cases** pass exact AST/artifact checks. Additional residual
  regressions preserve concat, send, unsafe arithmetic, ecrecover and environment
  designators without adding general source builtin inference.
- Fold deletion and well-formed Int-777 poisoning produce identical normalized
  modules, checker artifacts and equations. Source-derived typing has separate
  inferred-claim adversarial tests; residual type claims remain explicitly
  inherited, not falsely called metadata-independent.
- Independent meanings cover all **36 constant dependency environments and 40
  original bodies**, including constructors. `sourceOrdinaryProgramMeaningTest`
  kernel-links each original declaration, actual ordinary runtime declaration
  and complete body computation. Nine actual compile/body compositions use the
  same artifacts. The stated `get_tenv cx = FEMPTY` fixture premise remains.
- Checker-derived MethodId/Exp/Exp-AugAssign facts replace those source-domain
  whitelist premises. `sourceOrdinarySupport` exposes this at the clean ordinary
  checker/compiler boundary using the transparent `source_program_remainder`.
  The Exp-specific admission is replaced by `checked_power_run`,
  `binop_frag_pow` and `compile_power_case_sim`.

The relevant proof and boundary ledger is in
[ISSUE_543_COVERAGE.md](ISSUE_543_COVERAGE.md), with a checklist in
[.agent-files/issue543-scoped-checklist.md](../.agent-files/issue543-scoped-checklist.md).
The ordinary API and remaining trust are documented in
[frontend/sourceOrdinaryBridge.md](../frontend/sourceOrdinaryBridge.md).

## Legacy trust boundary follow-up

The legacy trust boundary is frozen at pre-branch behavior. Branch-added generic
`with_folded` wrappers on `BinOp`, `Compare`, `BoolOp`, `UnaryOp` and `Call` in
`jsonASTLib`, and the folded-following rule in `json_expr_int_opt`, are removed
in favor of the HOL source evaluator. This does not eliminate older remaining
metadata consumers. Fail-closed ABI checks remain. Legacy APIs do not acquire
source-normalization guarantees by trusting additional compiler replacements.

Post-removal validation passes at tactic timeout **2.5**, without skipping
goalfrag: five focused decoder/iterator/claims targets
(`.agent-files/issue135-remove-wrappers-build.log`) and seven integration targets
(`.agent-files/issue135-remove-wrappers-source4.log`). These cover both 26-case
ordinary acceptance inventories, all 36 valid retained programs, invalid originals
with poisoned folds, and nine exact deploy/runtime parity certificates. The 12
requested targets' build logs contain no CHEAT warnings. The unrestricted parallel
attempt was killed; the serial retry was stopped after successful targets to
continue with two workers. Neither interrupted command is a whole-command success.

## Necessary semantic/proof repairs

HOL follows pinned ABI aliasing: complex local arguments retain locations until
staging, indices are captured once, and non-memory complex arguments snapshot
on unwrap. Local/immutable arenas are separately scoped without undoing logical
writes. The actual evaluator and CPS encode `([True], False)` for the alias
witness, matching pin execution. Ordinary expression lists retain snapshots.

Constructor projected immutable mutations follow the pin; direct/runtime bans
remain appropriate. The pin's projected-Pop Venom panic is not source rejection
or successful compilation. The pure evaluator's obsolete eager ABI equations
were repaired, retaining its unrestricted forward and pure reverse theorems.
Affected low-level, typing, 11-way evaluator/storage/ExtCall and CPS proofs build.

## Parity and retained external boundaries

- Required seven and **all nine ordinary deploy/runtime certificates pass**.
- Fresh retained37 probe: **32 matches, four external failures, one expected
  rejection; aggregate exit 1**, not global green.
- Both power-overflow witnesses revert for both producers: **4/4 REVERTs**.

The four failures remain owned by #563 (two immutable backend `NONE`s),
#554/#551 (`raw_call`) and #567/#551 (`raw_revert`). See
[SOURCE_MODULE_PARITY_RESULTS.md](SOURCE_MODULE_PARITY_RESULTS.md).
They do not excuse a frontend rejection and are not counted as passing parity.

The old whitelist definitions remain for raw/backend consumers. The checked
ordinary wrapper does not ask callers for redundant MethodId/Exp gates. Local
tuple-base protection (#571) and broad ABI lowering protection (#551) remain;
their independent backend simulations were not inferred from source folding or
removed. ExpMod and unrelated arithmetic/call/storage/deployment admissions also
remain. In particular `source_module_checked_runtime_correct` inherits an old
lowering admission and is **not** a new cheat-free compiler correctness theorem.

## Final validation receipts

These historical receipts predate the legacy trust-boundary follow-up above;
they do not validate that change. Current follow-up validation is recorded above.

Use `.agent-files/.holbuild-toolchain/bin/holbuild` (0.11.7), tactic timeout
**2.5**, without skipping goalfrag.

- `issue543-final-forced.log`: seven ordinary core/composition targets forced,
  no cache/checkpoints, successful (175.456s aggregate).
- `issue543-final-forced2.log`: final residual-definition and composition
  changes forced again (106.076s aggregate).
- `issue543-final-combined4.log`: 23 scoped frontend, strict, meaning, support,
  evaluator/storage/ExtCall, pure/CPS, ABI typing and Exp targets successful
  (882.493s aggregate; cached targets distinguished from rebuilt targets).
- `issue543-ordinary-support.log`: clean ordinary checked/compiler whitelist
  discharge, kernel-audited without admissions.
- `issue543-final-export-audit3.log`: final audit, **66 theories / 1,842 closed
  exports**, plus checked compiler equations and Exp-specific simulations.
  Includes the clean ordinary support boundary; inherited runtime composition
  and unrelated backend admissions are explicitly excluded.
- `issue543-final-source-manifest.json`: 2,340 implementation/input files after
  scratch cleanup and whitespace-only formatting; receipt hashes retained. SHA256
  `f7b9c691c8f6ded9ddc2ece31c9648551a10ed8258279d3a2c214fcaaeae9599`.
  The executed-proof snapshot is preserved separately as
  `issue543-pre-cleanup-source-manifest.json`; cleanup did not rerun the proofs.
- `issue543-final-parity/`: independent producer, retained37, overflow, manifests
  and scoped certificate audits. The final residual-designator preservation
  changes were subsequently rechecked against all 26/36/9 inventories and the
  40-body ordinary composition; they do not change those compiler inputs.

Paths above are under `.agent-files/`. Earlier interrupted commands and stale
artifact refreshes remain in receipts; they are not reported as successful
whole commands. Builds have no new CHEAT warnings. Audits reject hypotheses,
axioms and non-bookkeeping oracles; the explicitly inherited runtime correctness
admission and unrelated backend simulations are excluded, not concealed.
