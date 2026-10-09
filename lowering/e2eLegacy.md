# Pre-§5.5 e2e compatibility removal ledger

TASK049, base `ace9f467`. **Final removal owner: TASK056.** TASK054 replaces
composition; TASK051 replaces the old source-unit contract. This is temporary
compatibility, not an old/new equivalence or a correctness certificate.

`e2eDefs` owns the exact clean §5.5 boundary. `e2eLegacyDefs` imports it for
concrete logs, then preserves the old definitions under explicit `_legacy`
names. It does not import `vyperLoweringCorrect` or `e2eCorrectness`.
The dependency direction is source/frame/syntax → e2eDefs → e2eLegacyDefs →
e2eCorrectness → configuredE2ECorrectness. No Venom theory imports lowering.
TASK048's clean `unitTransformDefs` API is unchanged; its old stronger contracts
below are NOT aliases of that API.

## Definition ledger

All 11 definitions listed for deletion at the end of PLAN §5.5 are here,
plus the old deployment/entry/call predicates, TASK048 contracts and source-unit
contract. Old RHS schemas are identical modulo identifier renaming; no new
boundary premise was added to an old claim.

Paths: **D** = `lowering/e2eDefsScript.sml` (old owner), **C** =
`lowering/e2eCorrectnessScript.sml`, **L** = `lowering/e2eLegacyDefsScript.sml`,
**O** = `lowering/configuredE2ECorrectnessScript.sml`.
Counts are active whole-identifier **constant / `_def` tokens**, including
owner declarations and recursive clauses, excluding comments and the private
saved-object checker. Omitted paths have zero occurrences. They are a removal
worklist, not logical evidence; recount when TASK051/054/056 migrate consumers.

| Old definition | Old → current owner | Current name | Remaining path counts |
|---|---|---|---|
| `run_call` (local) | C → L | `run_call_legacy` | L 1/1; C 1/0 |
| `vyper_evm_correspondence` | D → L | `vyper_evm_correspondence_legacy` | L 1/1; C 3/1; O 1/0 |
| `state_effects_match` | D → L | `state_effects_match_legacy` | L 2/1; C 0/1 |
| `state_unchanged` | D → L | `state_unchanged_legacy` | L 1/1; no outside client |
| `return_data_encodes` | D → L | `return_data_encodes_legacy` | L 3/1; C 0/1 |
| `initial_evm_rel` | D → L | `initial_evm_rel_legacy` | L 1/1; C 1/1 |
| `valid_function_call` | D → L | `valid_function_call_legacy` | L 1/1; C 1/1 |
| `finalizer_correct` | D → L | `finalizer_correct_legacy` | L 1/1; C 2/0; O 1/0 |
| `call_result_matches` | C → L | `call_result_matches_legacy` | L 1/1; C 1/0 |
| `caller_pre_logs` | C → L | `caller_pre_logs_legacy` | L 3/1; no outside client |
| `call_state_rel` | C → L | `call_state_rel_legacy` | L 1/1; C 3/2; O 1/0 |
| `valid_vyper_call` | C → L | `valid_vyper_call_legacy` | L 1/1; C 2/0; O 1/0 |
| `source_deployment_rel` | D → L | `source_deployment_rel_legacy` | L 1/1; C 2/0; O 1/0 |
| `ctx_transform_correct_legacy` | D → L | unchanged | L 2/1; C 0/1 |
| `checked_unit_transform_correct_legacy` | D → L | unchanged | L 1/1; C 3/1; O 1/0 |
| `source_unit_execution_correct` | C → C | `source_unit_execution_correct_legacy` | C 5/3; O 1/0 |

`compiled_event_info_def` moves C → D with exactly its old text/schema. It is
not obsolete. `logs_correspond` and its concrete-event proofs remain in D.
The clean `run_call` is Verifereum's, not an alias of the local legacy loop.

## Theorem clients and proof provenance

- C's private adapters become `call_state_rel_initial_evm_rel_legacy` and
  `valid_vyper_call_valid_function_call_legacy`: exact old claims/proofs modulo
  the legacy identifiers, no outside users. Remove both at TASK056 (the two
  local lemmas in §5.5's end list).
- C's `source_unit_execution_correct` theorem and private
  `source_unit_execution_through_pipeline` retain the old source-unit claim;
  TASK051/054 migrate them, TASK056 removes this compatibility contract.
- C's `e2e_vyper_to_evm` and `vyper_call_correct`, and O's
  `e2e_vyper_to_evm_O1`, keep their public names and exact old hypotheses and
  conclusions modulo the explicit legacy identifiers. Original proof text is
  preserved in source. **All three retain inherited admission tags through
  `codegen_correct_legacy`; none is certified as unadmitted.**
- C's existing local `evm_correspondence_to_call_result` cheat is unchanged,
  still explicitly admitted, not used to certify the new boundary. TASK054/056
  replace/remove it; do not pretend an alias repairs it.
- C's independent `e2e_venom_pipeline`, `compile_vyper_runtime_bytecode` and O's
  two phase/compose theorems remain unchanged and build. The tautological old
  deployment statement is unchanged, not claimed as deployment correctness.
- The definitionless `vyperLoweringHol` and `vyperHol` interfaces import C/O
  transitively and mention none of these predicates directly. Their dependency
  edges are preserved; they are not local build targets (TASK060 full closure).

TASK056 removes all above compatibility definitions, private adapters and
commented pre-5.5 provenance **after** replacing their consumers, not by a
bridge between the boundaries. No old claim or known client is waived here.
