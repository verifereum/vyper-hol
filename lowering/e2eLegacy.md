# TASK056 completed compatibility-retirement ledger

Baseline: `2fc79cd70d2e05e3047a41453232c8e0e3104966` (combined TASK053–055).
This is a **completed retirement/provenance ledger**, not a live legacy API.
All counts/names below concern compiler/call compatibility, not unrelated
historical pass implementations. There is no old/new equivalence bridge.

## Original text and proof identities

Original statements/proofs are retained verbatim in inactive SOURCECOMMENT
archives in `lowering/e2eCorrectnessScript.sml`,
`lowering/configuredE2ECorrectnessScript.sml`,
`lowering/vyperLoweringCorrectScript.sml`, and
`venom/codegen/codegenCorrectnessScript.sml`. Earlier original proof text inside
those archives is retained too. No old proved claim has been newly admitted.
The two deleted owners are externally retained exactly at:

- `2fc79cd7:lowering/e2eLegacyDefsScript.sml` (15 definitions, no theorems);
- `2fc79cd7:semantics/vyperEntryCompatScript.sml` (one definition, two proved
  projection theorems; TASK027/028 compatibility helper).

Git source identities above retain the entire original text, not reconstructed
summaries. The following tables map every retired active export/helper to its
planned replacement. Replacements are new contracts, **not equivalences**.
No pending retirement remains in this ledger.

## All 21 retired definitions (including all PLAN §5.5 obsolete constants)

| Baseline owner / retired definition | Replacement / reason |
|---|---|
| e2eLegacyDefs: `ctx_transform_correct_legacy` | `unitTransformDefs$ctx_transform_correct`, forward terminating-run simulation |
| e2eLegacyDefs: `checked_unit_transform_correct_legacy` | `unitTransformDefs$checked_unit_transform_correct`, same initial state |
| e2eLegacyDefs: `finalizer_correct_legacy` | identity finalizer `K SOME`, `finalize_codegen_identity` and L1 |
| e2eLegacyDefs: `source_deployment_rel_legacy` | exact singleton main module / layouts `e2eDefs$source_deployment_rel` |
| e2eLegacyDefs: `return_data_encodes_legacy` | `return_bytes`, including ABI single-dynamic-value wrapping |
| e2eLegacyDefs: `state_effects_match_legacy` | success clause of `call_result_rel`, concrete events and requests |
| e2eLegacyDefs: `state_unchanged_legacy` | explicit failure `frame_outcome`, no fabricated source-success effects |
| e2eLegacyDefs: `vyper_evm_correspondence_legacy` | `call_result_rel`, frame-aware `run_call`, not whole-transaction `run` |
| e2eLegacyDefs: `initial_evm_rel_legacy` | L8 `entry_venom_state_initial_ctx_rel` |
| e2eLegacyDefs: `valid_function_call_legacy` | exact `valid_vyper_call`, no selector-table compatibility obligation |
| e2eLegacyDefs: `run_call_legacy` (old LOCAL run_call) | Verifereum `vfmExecution$run_call`, totality `run_call_total` |
| e2eLegacyDefs: `call_state_rel_legacy` | live transferred accounts / fresh head-frame `call_state_rel` |
| e2eLegacyDefs: `valid_vyper_call_legacy` | `valid_vyper_call tops tx calldata ret` |
| e2eLegacyDefs: `caller_pre_logs_legacy` | residual caller logs inside `frame_outcome` |
| e2eLegacyDefs: `call_result_matches_legacy` | `call_result_rel` / explicit exceptional-frame outcomes |
| e2eCorrectness: `source_unit_execution_correct_legacy` | `vyperLoweringCorrect$source_unit_execution_correct`, oracle triple |
| vyperLoweringCorrect: `external_logs_rel` | `logs_correspond` / concrete ordered events in clean result relation |
| vyperLoweringCorrect: `external_call_state_rel` | success observables in `external_call_result_rel`; entry environment in L6 |
| vyperLoweringCorrect: `external_call_result_rel_legacy` | exact oracle-mode `external_call_result_rel`; no fuel-zero acceptance |
| codegenCorrectness: `initial_ctx_rel_legacy` | exact live-frame `initial_ctx_rel`, L8 |
| vyperEntryCompat: `call_external_simple` | full `call_external NONE am tx` triple; no hidden pair alias |

The corresponding `_def` exports are all retired too. `e2eLegacyDefs` and
`vyperEntryCompat` have no live users and their entire script owners are deleted.
`initial_state am scs` remains the original TWO-argument API, with NONE outcomes
and empty requests inherited through the source-oracle state; no record layout,
compiler, emitter, fixture or test expectation changes.

## All 14 retired active theorem/helper claims

| Baseline theorem/helper | Replacement / consumer migration |
|---|---|
| e2eCorrectness: `call_state_rel_initial_evm_rel_legacy` (local) | L6/L8 on exact shared `entry_venom_state` |
| e2eCorrectness: `valid_vyper_call_valid_function_call_legacy` (local) | direct `valid_vyper_call` in S1/S3, concrete entry calldata |
| e2eCorrectness: `log_entry_equiv_log_entry_corresponds` (local) | existing concrete-event equality theorems in e2eDefs |
| e2eCorrectness: `external_logs_rel_logs_correspond` (local) | clean lowering success clause uses `logs_correspond` directly |
| e2eCorrectness: `source_unit_execution_correct_legacy` | clean source-unit definition consumed by §8.1/§2.1 |
| e2eCorrectness: `run_context_zero_error` (local) | `external_call_result_rel_terminates` / nonterminal rejection, not fuel zero |
| e2eCorrectness: `source_unit_execution_through_pipeline` (local) | `ctx_transform_correct_forward` plus clean result transport |
| e2eCorrectness: `e2e_vyper_to_evm_legacy` | exact admission-free `e2e_vyper_to_evm` (§8.1) |
| e2eCorrectness: `evm_correspondence_to_call_result` (local, direct admission) | frame-aware generic composition; removed, not proved by alias |
| e2eCorrectness: old `vyper_call_correct` | exact §2.1 public theorem, S1–S7 only |
| configuredE2ECorrectness: `e2e_vyper_to_evm_O1` | exact §2.1 O1 top theorem; wrapper no longer configured |
| codegenCorrectness: `codegen_correct_legacy` (direct admission) | planned S7 `codegen_correct`, real frame/resource-starvation conclusion |
| vyperEntryCompat: `call_external_simple_projection` | full NONE-mode entry regressions `entry_none_cv`, body requests / rollback |
| vyperEntryCompat: `call_external_simple_cases` | direct case splits on full entry triple; NONE/SOME CV regressions |

The already-inactive `vyper_to_venom_correct`, symbolic-log encoder lemmas and
vacuous deployment placeholder remain source provenance only; they introduce
no saved export or new admission. Symbolic-log replacements are
`log_entry_equiv_concrete_event` and `log_entry_corresponds_concrete_event`.
The real §5.11 `e2e_deploy_correctness` remains its separately classified planned
admission, OFF the call path, as does `gen_fn_simulation`.

## Preserved proved public schemas / original proof owners

- `e2eCorrectness$e2e_venom_pipeline`: original schema/proof unchanged.
- `e2eCorrectness$compile_vyper_runtime_bytecode`: original schema/proof unchanged.
- `configuredE2ECorrectness$compile_vyper_with_success_phases`: original schema;
  original proof in lower acyclic `compilePhasesProps` owner, modern Theorem re-export.
- `configuredE2ECorrectness$compile_vyper_with_deploy_runtime_compose`: likewise.

No `save_thm`, `prove` or `mk_thm` re-export and no compatibility equivalence.

## Known clients and audits

`e2eCompositionChecks` now checks the new top and real deployment as CLASSIFIED
STAGES (Hyp=0/no axioms, admission tags honest), never clean certificates.
`vyperOracleEntryTest` drops the unused deleted ancestor and uses full NONE/SOME
entry results; all its original theorem statements/proofs remain unchanged.
`configuredE2ECorrectness` retains only its two proved phase interfaces.
The entry/producers/composition/deployment checks use only the clean boundaries.
Definitionless `vyperLoweringHol`/`vyperHol` mention no retired constant: full
rollup acceptance is TASK060 debt, not part of this local gate.

Source admission delta: 130 → 128, removing precisely the local
`evm_correspondence_to_call_result` site in e2eCorrectness and
`codegen_correct_legacy` site in codegenCorrectness. No baseline pass/function
simulation admission is removed. Final built top must report exactly S1–S7;
generic and each L1–L13 must report no admission dependency. Evidence and exact
local acceptance status are recorded in `/tmp/m1-result-056.md`; later TASK057–059
documentation and TASK060 full integration/parity are separate obligations.
