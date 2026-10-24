# Selfdestruct boundary probes and migration interface

This records the pre-migration checkout and the boundary probes used to plan
the semantics change. The prospective wording and source locations below are
historical. The implemented semantics and source/CPS regressions are in
`vyperInterpreterScript.sml`, `vyperSmallStepScript.sml`,
`vyperSystemHaltTestScript.sml` and `vyperDeletionTransportTestScript.sml`.

`vyperSelfdestructBoundaryTheory` tests the account layer before introducing
`HaltException`. All eight theorems are kernel-closed (the tag audit in the
script prints only DISK_THM). No supported-language restriction changes here.

## Shared action interface for big-step and CPS

The coordinated semantics change should expose one action taking `(cx, to)`:

1. Read accounts and the executing address `self = cx.txn.target`.
2. Apply `vfmExecution$transfer_value self to original_balance` with
   `update_accounts`. Do **not** use the interpreter's checked transfer.
3. If `cx.txn.created_in_tx`, zero the executing account's balance and prepend
   `self` to pending deletions. Otherwise leave the queue unchanged.
4. Raise `HaltException`, never `Value NoneV`.

The tested equations are independent of the new datatype/record fields:
`old_self_beneficiary` covers the old/self case; `new_self_beneficiary` plus
`zero_self_balance` covers new/self; `transfer_full_balance` covers other
beneficiaries, including a zero original balance. `zero_self_preserves_other`
shows the extra new-contract zeroing cannot undo the recipient credit.
`vfm_deletion_cons` proves Verifereum conses deletions. Consequently the observer
must save the old queue LENGTH and recover the new prefix with
`TAKE (LENGTH post - old_length) post`, as proved in
`deletion_prefix_observation`. Logs, unlike deletions, currently use DROP.
`finalize_accounts` exposes the existing transaction commit boundary.

The actual VFM step also checks static mode and gas, sets empty returndata and
finishes the frame. The source action should model its account/deletion/halt
part, not introduce checked source-transfer overflow or self-transfer rules.

## Concrete C3.3 migration sites (pre-migration source)

- `semantics/vyperStateScript.sml`: exception datatype. `finally` (235) always
  runs the same cleanup on INL and INR, so merely adding a halt case to
  `handle_function` is insufficient to preserve nonreentrant locks.
- `semantics/vyperContextScript.sml`: `call_txn` and `empty_call_txn`; constructor
  context must set creation true. Existing updates inherit the field; complete
  record literals require migration.
- `semantics/vyperInterpreterScript.sml`: `handle_function` (257) currently
  maps unknown controls to TypeError; its cv translation must gain halt.
  `handle_loop_exception` propagates unknown exceptions unchanged.
  IntCall (1442-1451) uses unconditional finally(pop_function; unlock): replace
  this with result-sensitive cleanup, restoring scopes on all outcomes but
  skipping unlock on halt. SelfDestructTarget (1494) currently returns NoneV.
  `call_external_function` (1855-1874) must commit halt before its generic INR
  rollback case, bypassing unlock/cast. `call_external` (1974) must finalize
  halt as well as INL. `load_contract` (2028-2033) must mark creation true and
  treat constructor halt as a committed INL machine without installing sources.
- `semantics/vyperSmallStepScript.sml`: SelfDestructK application (816),
  apply_exc IntCallK2 (432-449), and apply IntCallK2 (353) share the same cleanup
  semantics. The `apply_exc` and eval correspondence proofs around 1619-1684
  currently unfold finally; migrate together with the helper interface.
- `semantics/prop/vyperExprNoControlScript.sml`: expression no-control must allow
  halt (but must still exclude Return/Break/Continue). Its handle_function
  lemma and selfdestruct induction branch need the new permitted constructor.
- Scope/preservation consumers in `vyperEvalPreservesScopesScript.sml`,
  `vyperScopePreservationScript.sml`, `vyperStatePreservationScript.sml`,
  `vyperTypeEvalStoragePreservationScript.sml`: unconditional-finally internal
  call patterns must use a scope-restoration boundary for the new cleanup.
- `semantics/prop/vyperTypeSelectedEntrySoundnessScript.sml` defines a duplicate
  `call_external_body` (36-75): add the committed halt branch here too, or
  `call_external_function_body` ceases to hold. `vyperTypeSelectedEntryScript.sml`
  exposes the wrapper result case and must include halt finalization.
- `vyperTypeExternalCallMachineScript.sml` has generic INR rollback claims
  (320,352,365,372) which become false for halt: restrict their failure premise
  with `exc <> HaltException`; successful halt needs the corresponding machine
  preservation case. `vyperTypeDeploymentMachineScript.sml` and deployment
  success-case helpers consume load_contract's old case partition.
- Tests `vyperOracleEntryTestScript.sml` (109) and
  `vyperOracleIntegrationTestScript.sml` (190) also claim generic INR rollback;
  distinguish halt. `tests/vyperTestRunnerScript.sml` invokes load_contract (210)
  and call_external (293): runtime halt is success with empty returndata, not a
  rollback/error. Audit downstream result expectations in that runner.
- E2E consumers: `lowering/e2eDefsScript.sml`, `e2eCorrectnessScript.sml`,
  `vyperLoweringCorrectScript.sml`, `proofs/e2eCompositionScript.sml`,
  `tests/e2eBoundaryTestScript.sml`: exception case partitions must include halt.
  Their relation extensions are scheduled in C5, but any break caused by the
  definition migration needs repair in the migration stable point.

## Concrete C3.4 observer/deletion sites

- `venom/codegen/frame/callTraceScript.sml` currently has
  `pending : (call_request # num) option` (22), storing only pre-call log count.
  Extend it with pre-call deletion count. Both immediate outcome (80) and
  deferred completion (88-90) must pass this count to outcome_of (58).
- `co_logs := DROP n c.logs` is not the deletion convention: co_toDelete must
  use TAKE/new-prefix. Failed and precompile outcomes carry an empty prefix.
- Migrate `extCallOracle` outcome literals and source `vyperCallOutcome`
  adoption together. Only successful non-static adoption prepends deletions.
- Interpreter direct `extract_call_result`, raw_call, ExtCall and send must
  transport successful callee final_state.rollback.toDelete. Do not apply
  process_deletions early: `finalize_pending_deletions` is the commit boundary.

The pinned checkout currently lacks the coordinated cr_gas/cr_data_len/cr_kind
and co_created fields mentioned by the task; preserve any arriving changes
rather than assuming those fields already exist.
