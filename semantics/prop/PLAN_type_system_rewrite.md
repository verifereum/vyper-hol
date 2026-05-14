# PLAN: Complete fresh Vyper type-system soundness rewrite

## Argument

The fresh stack is sound by a strongest-joint-invariant architecture. Each evaluator-recursive layer proves one combined result: no `Error (TypeError s)` plus the relevant preservation of state, accounts, environment consistency, runtime value/result typing, and exceptional/return typing. Public no-TypeError and preservation theorems are projections only.

The current lynchpin is assignment target execution. `assign_target_sound_mutual` has already been strengthened with the right runtime side conditions: `assign_operation_matches_target_shape` and `assign_target_assignable_context`. These side conditions make the remaining target branches true: top-level storage/hashmap/array writes have explicit writability/layout witnesses, tuple assignment has shape and component alignment, and update/append/pop operations have operation-specific runtime typing. Once the remaining assignment mutual branches are proved, statement assignment cases do not re-analyse assignment semantics; they derive the strengthened side conditions from statement typing and evaluated targets, then apply the joint assignment theorem.

Builtin/binop obligations are localized but strict prerequisites for expression soundness and the update-assignment path. They must align executable builtin evaluation with internal typing predicates (especially ABI encode bounds and `Env MsgGas` if still mismatched in current source), without adding public side conditions. Statement and call layers then complete by consuming the joint invariants and exporting only compatibility wrappers. Final completion is exactly: `holbuild build vyperSemanticsHolTheory` succeeds with no reachable CHEAT warnings in the fresh stack.

## Definition Design

### Existing `assign_operation_matches_target_shape`
- Purpose: states runtime compatibility between an evaluated assignment target value and the requested assignment operation.
- Shape: case split on target value/operation; tuple target assignment should force tuple replacement with aligned component lengths, while base targets admit scalar update/replace/append/pop according to operation typing.
- Boundary: statement proofs should derive this via boundary lemmas, not by unfolding assignment evaluator internals.
- Probes: C3.4 and C5 test tuple shape and statement derivability.
- Failure signs: tuple branches require manual component reconstruction or missing length equalities after applying the predicate.

### Existing `assign_target_assignable_context`
- Purpose: names runtime writability/assignability of an evaluated target, including scoped assignability and top-level storage/hashmap layout witnesses.
- Shape: structural over assignment target values; tuple targets lift componentwise; top-level targets require module code, declaration/layout success, and for hashmaps nonempty subscript information.
- Boundary: top-level branch helpers may unfold it, but statement proofs should use C5 lemmas.
- Probes: C3.1/C3.2 verify sufficiency for `HashMapRef`/`ArrayRef`; C5 verifies derivability from target evaluation and statement typing.
- Failure signs: statement typing and runtime consistency cannot provide declaration/layout witnesses. Escalate rather than weakening `assign_target_sound_mutual`.

### Existing `target_assignment_values_assignable`
- Purpose: aligns tuple/list targets, RHS/materialized values, runtime types, value typing, and assignable contexts with `assign_targets` recursion.
- Shape: list relation with head/tail decomposition matching the evaluator.
- Boundary: tuple/list statement branches should consume it directly; do not rebuild with ad hoc indexes.
- Probes: C3.4, C3.5, and C5.
- Failure signs: after assigning the head, tail premises cannot be re-established in the intermediate state; this would indicate the relation or preservation invariant is too weak.

### Existing `assignable_type`
- Purpose: static exclusion of `NoneT` through assignable aggregate types.
- Shape: recursive over Vyper type syntax, with boundary facts `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV`.
- Boundary: AnnAssign/materialization proofs use these lemmas instead of local non-None cheats.
- Probes: C5 AnnAssign side-condition lemmas.
- Failure signs: AnnAssign still needs an extra non-None premise not derivable from `assignable_type`.

### Builtin/ABI/runtime typing definitions
- Purpose: ensure each internally well-typed builtin/type-builtin/binop runtime branch cannot return `TypeError` and successful results have the declared type.
- Shape: local constructor case interfaces in `vyperTypeBuiltinsScript.sml`.
- Boundary: public soundness wrappers must not gain ABI-size or `MsgGas` exclusions; any needed restrictions or runtime support are internal repairs.
- Probes: C1, including current ABI encode probe lemmas.
- Failure signs: a concrete internally well-typed builtin call still evaluates to `Error (TypeError s)`.

## Code Structure

Preserve the current fresh-stack split.

- `vyperTypeSystemScript.sml`: edit only for strict internal typing/result predicate repairs needed by C1.
- Runtime/evaluator files: edit only if choosing runtime support rather than typing exclusion for a currently mismatched builtin such as `MsgGas`.
- `vyperTypeBuiltinsScript.sml`: all builtin/binop/type-builtin local no-TypeError and success-typing proofs.
- `vyperTypeStatePreservationScript.sml`: assignment subscript helpers, top-level branch helpers, and remaining `assign_target_sound_mutual` resumes.
- `vyperTypeAssignSoundnessScript.sml`: compatibility wrappers as corollaries of the joint assignment theorem.
- `vyperTypeStmtSoundnessScript.sml`: statement-level side-condition lemmas and `eval_all_type_sound_mutual` integrations.
- `vyperTypeCallSoundnessScript.sml`: call/callable-body setup lemmas and wrapper projections.
- `vyperTypeSoundnessNewScript.sml`: final public theorem surface only.

Do not edit retired old theories (`vyperTypeSoundnessDefs`, `vyperTypeSoundnessHelpers`, `vyperTypeSoundness`) unless the C0 build/audit proves they are imported transitively by `vyperSemanticsHolTheory`.

## Components

### C0: Reachable fresh-stack cheat audit
- Statement: Run `holbuild build vyperTypeStatePreservationTheory` and `holbuild build vyperSemanticsHolTheory`; record every CHEAT warning reachable from `vyperSemanticsHolTheory` in the fresh stack and map it to C1–C9.
- Approach: mechanical build/grep audit before edits; stop if a reachable current-source cheat is not covered.
- Dependencies: none
- Risk: 1
- Risk rationale: mechanical audit.
- Checkpoint: yes
- Not to try: repository-wide cleanup.

### C1: Localized builtin/binop/type-builtin soundness
- Statement: In `vyperTypeBuiltinsScript.sml`, discharge all reachable cheats including current-source equivalents of `well_typed_binop_no_type_error`, `well_typed_binop_success_type`, `well_typed_builtin_app_no_type_error`, `well_typed_builtin_app_success_type`, `well_typed_type_builtin_no_type_error`, and `well_typed_type_builtin_success_type`; repair ABI encode bound and `Env MsgGas` internally if current source still has those mismatches.
- Approach: local constructor case splits; use existing arithmetic/ABI/bytes lemmas. ABI encode must carry a real encoded-size bound; `MsgGas` must either be supported at runtime or excluded internally from the well-typed cases.
- Dependencies: C0
- Risk: 2
- Risk rationale: localized, non-evaluator-recursive obligations; internal helper statements are not frozen.
- Checkpoint: yes
- Not to try: hidden assumptions about ABI bounds; redoing builtin proofs later.

### C2: Assignment update/subscript leaf soundness
- Statement: Prove current-source versions of `well_typed_update_binop_no_type_error`, `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`.
- Approach: leaf-operation theorem first, then recursion-matching induction on `assign_subscripts`; route update operations through C1.
- Dependencies: C1
- Risk: 2
- Risk rationale: follows evaluator recursion once update-binop soundness exists.
- Checkpoint: yes
- Not to try: unfolding binop semantics here; weakening pop/append typing requirements.

### C3: Complete `assign_target_sound_mutual`
- Statement: Finish `sound_TopLevelVar` `HashMapRef`, `sound_TopLevelVar` `ArrayRef`, `sound_ImmutableVar`, `sound_TupleTargetV`, and `sound_assign_targets_cons` in `vyperTypeStatePreservationScript.sml`.
- Approach: keep exact branch helpers; integrate into existing resumes. C3.1–C3.5 are the executable subcomponents.
- Dependencies: C2
- Risk: 2
- Risk rationale: named local branches with strengthened premises already in place.
- Checkpoint: yes
- Not to try: broad `AllCaseEqs()` cleanup; weakening side conditions.

#### C3.1: TopLevelVar HashMapRef branch
Use assignable context for nonempty subscripts/layout, top-level hashmap declaration facts, strengthened hashmap key path typing, suffix assignment via C2, and storage read/write no-TypeError facts. Checkpoint after this branch helper.

#### C3.2: TopLevelVar ArrayRef branch
Split append/pop/ordinary element assignment immediately; dynamic-array facts handle append/pop, ordinary suffix assignment reduces to C2 plus typed storage write-back.

#### C3.3: ImmutableVar branch
Use immutable consistency/preservation helpers and C2 for subscript/leaf update no-TypeError.

#### C3.4: TupleTargetV branch
Use `assign_operation_matches_target_shape` to force tuple replacement/length agreement and `target_assignment_values_assignable` to call the list mutual theorem.

#### C3.5: assign_targets cons branch
Apply head IH to the real intermediate state, use preservation to re-establish tail premises, then apply tail IH; finalise the mutual theorem.

### C4: Assignment compatibility wrappers
- Statement: Prove reachable wrappers in `vyperTypeAssignSoundnessScript.sml`, including `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error`, or current-source strengthened equivalents used by callers.
- Approach: project from completed `assign_target_sound_mutual`; update callers to supply strengthened premises where old wrappers were underspecified.
- Dependencies: C3
- Risk: 2
- Risk rationale: corollary work from the joint theorem.
- Checkpoint: no
- Not to try: a second assignment induction.

### C5: Statement-level assignment side-condition lemmas
- Statement: Prove lemmas deriving `assign_operation_matches_target_shape`, `assign_target_assignable_context`, tuple/list `target_assignment_values_assignable`, and AnnAssign non-`NoneT` facts from statement typing/evaluation hypotheses.
- Approach: scoped cases use target assignability/env-preservation facts; top-level cases use declaration/layout consistency; AnnAssign uses `assignable_type` lemmas; tuple/list cases package aligned component facts.
- Dependencies: C3, C4
- Risk: 2
- Risk rationale: exactly the named blocker; should be structural if invariants are adequate.
- Checkpoint: yes
- Not to try: unfolding `assign_target_def` in statement proofs; weakening assignment soundness if witnesses are missing.

### C6: Assignment statement branches in `eval_all_type_sound_mutual`
- Statement: Close current cheated/suspended assignment cases, especially `AnnAssign`, `Assign`, `AugAssign`, and related append/tuple/list assignment branches.
- Approach: follow evaluator order; at assignment invocation, derive all strengthened premises via C5 and apply C3/C4. `AugAssign` uses C1/C2 for update operations.
- Dependencies: C1, C2, C3, C4, C5
- Risk: 2
- Risk rationale: integration after side-condition lemmas.
- Checkpoint: yes
- Not to try: duplicating assignment-target branch logic.

### C7: Remaining statement evaluator mutual cases
- Statement: Remove all remaining reachable `cheat`/`suspend` obligations inside `eval_all_type_sound_mutual` not covered by C6.
- Approach: branch-by-branch within the existing joint invariant, consuming expression soundness, builtin soundness, scope-pop, env-extension/preservation, assignment soundness, and call setup facts.
- Dependencies: C1, C6
- Risk: 2
- Risk rationale: standard branch integration under an already designed joint theorem.
- Checkpoint: yes
- Not to try: parallel no-TypeError-only evaluator proofs.

### C8: Call soundness wrappers
- Statement: Prove `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, `special_call_no_type_error`, and current-source callable-body wrappers required by the public surface.
- Approach: use completed statement/callable-body joint soundness plus narrow setup lemmas for defaults, env extension, account consistency, signatures, and scope restoration; wrappers are projections.
- Dependencies: C7
- Risk: 2
- Risk rationale: listed wrappers should not require new evaluator induction.
- Checkpoint: no
- Not to try: separate call no-TypeError/type-preservation proof trees.

### C9: Public wrappers and final zero-CHEAT build
- Statement: Preserve public wrappers equivalent in strength to `typed_stmts_no_type_error`, `typed_stmts_success_preserves_state_env`, `typed_stmts_exception_preserves_state_and_return_type`, `typed_expr_no_type_error`, `typed_expr_success_preserves_type`, and `typed_callable_body_no_type_error`; `holbuild build vyperSemanticsHolTheory` succeeds with zero reachable CHEAT warnings.
- Approach: keep `vyperTypeSoundnessNewScript.sml` as a projection layer. Final build/audit; any extra reachable fresh-stack cheat is an escalation with exact theorem/import path.
- Dependencies: C4, C7, C8
- Risk: 1
- Risk rationale: final corollary/build check after upstream components.
- Checkpoint: yes
- Not to try: weakening frozen public behavior; editing retired theories without reachability evidence.

## Dependency Graph

C0 gates the current audit. C0 → C1 → C2. C2 feeds C3.1–C3.4; C3.1–C3.4 → C3.5; C3 finalises the assignment mutual theorem. C3 → C4 and C5. C1, C2, C3, C4, C5 → C6. C1, C6 → C7. C7 → C8. C4, C7, C8 → C9.

## Notes

- The first proof-editing focus should be the TASK’s handover branches in `vyperTypeStatePreservationScript.sml`, but C1/C2 are strict prerequisites for any assignment path that reaches update-binop/subscript helpers.
- If C5 cannot derive `assign_target_assignable_context` for top-level targets from current static typing and runtime consistency, escalate with the exact residual goal. That is a missing invariant/interface fact, not permission to weaken `assign_target_sound_mutual`.
- If C1 exposes a concrete well-typed builtin that returns `TypeError`, use the TASK’s non-frozen internal-helper permission to repair internal typing/runtime alignment; do not add public exclusions.
- Old retired theories are context only unless C0 proves they are still reachable from `vyperSemanticsHolTheory`.

## Structured Components

### C0: Reachable fresh-stack cheat audit
- Kind: `audit_probe`
- Risk: 1
- Rationale: Mechanical holbuild/grep work needed to align the executor with current source; it does not change proof architecture.
- Checkpoint: yes

#### Statement
Run `holbuild build vyperTypeStatePreservationTheory` and `holbuild build vyperSemanticsHolTheory`; record every CHEAT warning reachable from `vyperSemanticsHolTheory` in the fresh stack and map it to the components below.

#### Approach
Use the TASK file as scope authority. Ignore old retired theories unless the build proves they are imported transitively by `vyperSemanticsHolTheory`. If a reachable current-source cheat is not covered by C2–C9, stop and escalate with the exact theorem name and import path.

#### Not to try
Do not start repository-wide cheat cleanup; the audit is only to prevent missing an in-scope reachable obligation.

### C1: Localized builtin/binop/type-builtin soundness
- Kind: `proof_cluster`
- Risk: 2
- Rationale: The TASK identifies these as localized builtin/binop obligations. They are constructor case analyses over builtin/operator typing and runtime definitions, with internal helper statements allowed to be repaired if current source exposes mismatches.
- Required for completion: yes
- Dependencies: C0
- Checkpoint: yes

#### Statement
In `vyperTypeBuiltinsScript.sml`, discharge all reachable cheats, including current-source equivalents of `well_typed_binop_no_type_error`, `well_typed_binop_success_type`, `well_typed_builtin_app_no_type_error`, `well_typed_builtin_app_success_type`, `well_typed_type_builtin_no_type_error`, and `well_typed_type_builtin_success_type`; preserve or repair the ABI encode bound and `Env MsgGas` behavior internally so typed builtin evaluation cannot return `Error (TypeError s)`.

#### Approach
Proceed by local case split on operator/builtin/type-builtin constructors. Use existing arithmetic/bytes/ABI helper lemmas where available (`Len_result_fits_uint256`, ABI encode size probes, integer bounds lemmas). For ABI encode, keep the internal result predicate strong enough to reject too-small bounds; for `Env MsgGas`, either prove the runtime branch typed/no-TypeError if implemented or repair the internal typing surface so the public theorem has no extra side condition.

#### Not to try
Do not assume hidden ABI size bounds. Do not reprove builtin facts inside assignment or statement soundness; later components must consume these theorems.

### C2: Assignment update/subscript leaf soundness
- Kind: `infrastructure_lemma_cluster`
- Risk: 2
- Rationale: These theorems follow the recursion of `assign_subscripts` once C1 supplies update-binop no-TypeError; the handover lists them as localized inherited prerequisites.
- Required for completion: yes
- Dependencies: C1
- Checkpoint: yes

#### Statement
In `vyperTypeStatePreservationScript.sml`, prove current-source versions of `well_typed_update_binop_no_type_error`, `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`.

#### Approach
First prove the leaf assignment-operation theorem: `Replace` uses value typing, `Update` uses C1 update-binop soundness, `AppendOp`/`PopOp` use the strengthened dynamic-array premise in `assign_operation_runtime_typed`. Then prove the subscript theorems by recursion-matching induction over `assign_subscripts`, carrying the evaluated leaf type, path typing, `assignable_type`/non-`NoneT` facts, and value typing through each path step.

#### Not to try
Do not unfold binop semantics in this file. Do not weaken `PopOp` to non-dynamic arrays or drop the strengthened operation runtime typing premise.

### C3: Complete `assign_target_sound_mutual` in state preservation
- Kind: `proof_cluster`
- Risk: 2
- Rationale: All remaining branches are named in the TASK and are local to the assignment mutual theorem. The difficult top-level storage `Value` branch is already proved, and the remaining branches should be exact branch-helper integrations under the strengthened side conditions.
- Required for completion: yes
- Dependencies: C2
- Checkpoint: yes

#### Statement
Finish all cheats inside `assign_target_sound_mutual` in `vyperTypeStatePreservationScript.sml`: `sound_TopLevelVar` `HashMapRef` case, `sound_TopLevelVar` `ArrayRef` case, `sound_ImmutableVar`, `sound_TupleTargetV`, and `sound_assign_targets_cons`. Do not weaken the theorem’s strengthened premises.

#### Approach
Preserve the current suspended mutual theorem structure. Add focused branch helper lemmas immediately before the relevant resumes when a branch requires multi-step semantic facts. Each helper should match one evaluator branch and conclude the exact no-TypeError/preservation fact needed by the resume; the main mutual proof should then be mostly dispatch and projection from C2 and existing all-result preservation facts.

#### Not to try
Do not use broad `gvs[..., AllCaseEqs(), ...]` across top-level `Value`/`HashMapRef`/`ArrayRef` branches. Do not remove `assign_operation_matches_target_shape` or `assign_target_assignable_context` from the theorem.

### C3.1: TopLevelVar HashMapRef branch
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The handover gives the exact mathematical route: assignable context supplies nonempty subscripts/layout; strengthened target path typing supplies key typing; C2 supplies recursive suffix soundness.
- Dependencies: C2
- Checkpoint: yes

#### Statement
Prove an exact helper/resume closing the `lookup_global ... = INL (HashMapRef is_transient base_slot kt vt)` branch in `assign_target_sound_mutual[sound_TopLevelVar]`.

#### Approach
Use `assign_target_assignable_context` to obtain `sbs <> []` and layout/slot witnesses for the top-level hashmap declaration. Connect the returned `HashMapRef` to `HashMapT kt vt` via top-level declaration/lookup consistency facts (`top_level_HashMap_decl` or current-source equivalent). Use `target_path_step_type` for the leading `ValueSubscript key` to discharge hashmap key evaluation and `value_has_type`; after `split_hashmap_subscripts`, bridge the remaining suffix to the hashmap value type and apply C2. Rule out storage read/write TypeErrors using `read_storage_slot_error` and typed write helpers.

#### Not to try
Do not attempt this inline before stating the branch helper. Do not destruct all declarations before eliminating impossible non-hashmap cases.

### C3.2: TopLevelVar ArrayRef branch
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: ArrayRef is a finite semantic case split: append, pop, and ordinary element/suffix assignment, all reducible to C2 plus storage write/read facts.
- Dependencies: C2
- Checkpoint: yes

#### Statement
Prove an exact helper/resume closing the `ArrayRef` branch in `assign_target_sound_mutual[sound_TopLevelVar]`.

#### Approach
Split immediately on the array operation path: special `AppendOp`, special `PopOp`, and ordinary element/path assignment through `resolve_array_element` or current-source equivalent. Use dynamic-array typing from `assign_operation_runtime_typed` for append/pop; for ordinary suffix assignment, identify the element leaf type and apply C2. Use existing typed storage write helpers to rule out TypeErrors on write-back.

#### Not to try
Do not merge array and hashmap reasoning. Do not assume append/pop are valid for static arrays.

### C3.3: ImmutableVar branch
- Kind: `proof`
- Risk: 2
- Rationale: Top-level storage/hashmap complications are absent; existing immutable preservation helpers and C2 should cover the branch.
- Dependencies: C2

#### Statement
Close `assign_target_sound_mutual[sound_ImmutableVar]`.

#### Approach
Use the already-proved all-result immutable preservation helper for state/env/account invariants. For no-TypeError, unfold only the immutable assignment branch, derive immutable value/type facts from runtime consistency, apply C2 to subscript/leaf updates, and use `set_immutable_preserves_*` helpers for successful writes.

#### Not to try
Do not import top-level storage/hashmap lemmas into this branch; they indicate the proof has split on the wrong target constructor.

### C3.4: TupleTargetV branch
- Kind: `proof`
- Risk: 2
- Rationale: The strengthened predicates were designed for this case: shape forces tuple replacement and `target_assignment_values_assignable` provides componentwise premises.
- Dependencies: C2

#### Statement
Close `assign_target_sound_mutual[sound_TupleTargetV]`.

#### Approach
Use `assign_operation_matches_target_shape` to reduce to the valid tuple replacement shape and obtain the component length agreement. Consume `target_assignment_values_assignable` to obtain per-component target runtime typing, value typing, and assignable context facts, then delegate to the `assign_targets` mutual theorem.

#### Not to try
Do not reconstruct tuple component typing by ad hoc list indexing if `target_assignment_values_assignable` can provide the aligned list facts.

### C3.5: assign_targets cons branch
- Kind: `proof`
- Risk: 2
- Rationale: This is the mutual list step; the only subtlety is transporting tail premises across the state returned by the head assignment, exactly what the joint all-result theorem provides.
- Dependencies: C3.1, C3.2, C3.3, C3.4
- Checkpoint: yes

#### Statement
Close `assign_target_sound_mutual[sound_assign_targets_cons]` and finalise `assign_target_sound_mutual`.

#### Approach
Split the head and tail premises from the componentwise relation. Apply the head assignment IH to the actual head result/state. Use the resulting runtime consistency and preservation facts to re-establish the tail premises in the intermediate state, then apply the tail IH. Combine no-TypeError results by the evaluator’s bind structure.

#### Not to try
Do not assume head assignment leaves the state unchanged. Do not start a separate induction over target lists outside the mutual theorem.

### C4: Assignment compatibility wrappers
- Kind: `compatibility_corollary`
- Risk: 2
- Rationale: Once C3 finalizes the joint assignment theorem, the listed wrappers are projections. Current callers may require compatibility names, but no new evaluator induction is needed.
- Required for completion: yes
- Dependencies: C3

#### Statement
In `vyperTypeAssignSoundnessScript.sml`, prove reachable wrappers `assign_target_no_type_error`, `assign_target_update_no_type_error`, `assign_target_append_no_type_error`, or current-source compatibility corollaries equivalent for callers.

#### Approach
Project no-TypeError from `assign_target_sound_mutual` under the strengthened premises. Where an old wrapper was underspecified, keep the old name only if its callers can supply the strengthened side conditions; otherwise update callers to use the joint theorem or a correctly strengthened compatibility corollary.

#### Not to try
Do not perform a second assignment evaluator proof. Do not hide missing side conditions with local assumptions.

### C5: Statement-level assignment side-condition lemmas
- Kind: `boundary_lemma_cluster`
- Risk: 2
- Rationale: The TASK identifies these as the precise blocker for statement assignment cases. They are structural consequences of statement typing, target evaluation, target assignment value relations, and env/assignability preservation facts.
- Required for completion: yes
- Dependencies: C3, C4
- Checkpoint: yes

#### Statement
In or near `vyperTypeStmtSoundnessScript.sml`, prove boundary lemmas deriving `assign_operation_matches_target_shape`, `assign_target_assignable_context`, tuple/list `target_assignment_values_assignable`, and AnnAssign non-`NoneT` facts from the current statement typing/evaluation hypotheses.

#### Approach
Package these facts once rather than deriving them inside each statement branch. For scoped targets, use `eval_base_target_*assignable*` and env-preservation assignability facts. For top-level targets, use runtime consistency plus declaration/layout facts to produce storage/hashmap writability witnesses. For `AnnAssign`, use `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV`. For tuple/list assignment, prove head/tail or all-list lemmas aligned with `target_assignment_values_assignable`.

#### Not to try
Do not unfold `assign_target_def` in statement proofs to prove context facts. If top-level declaration/layout witnesses cannot be derived, escalate; that is an invariant/interface gap, not permission to weaken assignment soundness.

### C6: Assignment statement branches in `eval_all_type_sound_mutual`
- Kind: `proof_cluster`
- Risk: 2
- Rationale: After C5, the assignment cases are integration with the existing strongest joint evaluator theorem and the completed assignment soundness theorem.
- Required for completion: yes
- Dependencies: C1, C2, C3, C4, C5
- Checkpoint: yes

#### Statement
In `vyperTypeStmtSoundnessScript.sml`, close current cheated/suspended assignment cases of `eval_all_type_sound_mutual`, especially `AnnAssign`, `Assign`, `AugAssign`, and assignment-related append/tuple/list branches still present in current source.

#### Approach
Follow evaluator order. At the exact state where `assign_target` or `assign_targets` is invoked, use expression/target soundness to obtain evaluated target/value typing, C5 to derive shape/context/assignability side conditions, and C3/C4 for assignment no-TypeError and preservation. For `AugAssign`, route update-operation facts through C1/C2.

#### Not to try
Do not duplicate `assign_target` case analysis inside statement soundness. Do not split no-TypeError and preservation into separate proof trees.

### C7: Remaining statement evaluator mutual cases
- Kind: `proof_cluster`
- Risk: 2
- Rationale: The TASK includes remaining suspended/cheated cases inside `eval_all_type_sound_mutual`. Under the existing joint invariant, non-assignment cases should be branch-local integrations of expression, scope-pop, env-extension, builtin, and call facts.
- Required for completion: yes
- Dependencies: C1, C6
- Checkpoint: yes

#### Statement
Remove all remaining reachable `cheat`/`suspend` obligations inside `eval_all_type_sound_mutual` not discharged by C6, including statement, statement-list, iterator, target, expression, and expression-list cases present in current source.

#### Approach
Work branch-by-branch within the existing mutual theorem. Consume already-proved expression target typing, env extension/preservation, scope-pop restoration, builtin soundness (C1), and assignment soundness (C3–C6). For call-expression cases, leave only obligations that genuinely require call-entry wrappers to C8 if the current source separates them; otherwise prove them directly from the joint statement/call infrastructure already in scope.

#### Not to try
Do not create parallel no-TypeError-only evaluator theorems. Do not touch retired old statement soundness theories unless C0 proves they are reachable.

### C8: Call soundness wrappers
- Kind: `compatibility_corollary_cluster`
- Risk: 2
- Rationale: The TASK lists four reachable call wrappers. They should be projections/setup lemmas from completed statement/callable-body soundness, defaults, env extension, account consistency, and scope restoration, not a new call evaluator proof tree.
- Required for completion: yes
- Dependencies: C7

#### Statement
In `vyperTypeCallSoundnessScript.sml`, prove `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, `special_call_no_type_error`, and any current-source callable-body wrapper needed by the public fresh surface.

#### Approach
Use the completed joint statement/callable-body invariant. Prove only narrow setup facts: function signature lookup, default argument typing, environment erasure/extension, account consistency, and scope restoration. Then project no-TypeError and preservation conclusions for each call form.

#### Not to try
Do not duplicate evaluator call-case analysis or prove separate no-TypeError and type-preservation call inductions.

### C9: Public wrappers and final zero-CHEAT build
- Kind: `final_integration`
- Risk: 1
- Rationale: Once upstream reachable cheats are removed, this is corollary maintenance and a build/audit check. Any missing reachable cheat is an escalation, not new strategy.
- Required for completion: yes
- Dependencies: C4, C7, C8
- Checkpoint: yes

#### Statement
Maintain public wrappers in `vyperTypeSoundnessNewScript.sml` equivalent in strength to `typed_stmts_no_type_error`, `typed_stmts_success_preserves_state_env`, `typed_stmts_exception_preserves_state_and_return_type`, `typed_expr_no_type_error`, `typed_expr_success_preserves_type`, and `typed_callable_body_no_type_error`; `holbuild build vyperSemanticsHolTheory` must succeed with zero reachable CHEAT warnings.

#### Approach
Keep `vyperTypeSoundnessNewScript.sml` as a projection layer from expression, statement, assignment, builtin, and call joint soundness theorems. Run final `holbuild`; if current source has additional reachable fresh-stack cheats not covered by C1–C8, report them with exact theorem names and dependency path before editing.

#### Not to try
Do not weaken frozen public behavior. Do not edit old retired theories unless they are actually imported transitively by `vyperSemanticsHolTheory`.

---

## PLAN AUGMENT: C3.1 @ 2026-05-14T03:21:03+00:00

# PLAN: C3.1 — prove `top_level_HashMapRef_assign_no_type_error`

## Argument

A top-level variable declared as `HashMapVarDecl is_transient kt vt` is looked up by `lookup_global` as the lazy storage reference `HashMapRef is_transient (n2w slot) kt vt`. Assignment to such a value cannot assign the hashmap object itself: the static target-path hypothesis `target_path_type env (HashMapT kt vt) sbs (Type ty)` forces `sbs <> []`. The first runtime subscript selects the outer hashmap slot; `split_hashmap_subscripts vt (TL (REVERSE sbs))` consumes any nested hashmap-key subscripts and leaves ordinary value subscripts `remaining` into the final storage value type.

The proof invariant for this branch is that the static path decomposition exactly matches the evaluator's HashMapRef do-block decomposition. Therefore: the first subscript exists; the nested hashmap split succeeds; all subscripts used by `compute_hashmap_slot` are value subscripts, so slot computation succeeds; the final Vyper source type evaluates to a runtime type value `final_tv`; and `leaf_type final_tv remaining` is exactly the runtime type for the assignment target `ty`.

Once the do-block reaches storage reading, `read_storage_slot` can fail only with a runtime error, not a TypeError. If it succeeds, storage decoding plus well-formedness gives `value_has_type final_tv current_val`. Then `assign_subscripts_no_type_error_runtime_typed` rules out TypeError from the nested value assignment, using the static operation typing and the non-`NoneTV` leaf condition from `assignable_type`. If the assignment succeeds, `assign_result_no_type_error_from_successful_assign` rules out a TypeError in the final return calculation.

## Definition Design

No definition changes are needed.

- `assign_target_def` is adequate: its TopLevelVar/HashMapRef branch names exactly the computations to prove successful (`first_sub`, `split_hashmap_subscripts`, `compute_hashmap_slot`, `evaluate_type`, `read_storage_slot`, `assign_subscripts`, `write_storage_slot`, `assign_result`). The proof should unfold it only in the branch lemma, not in the public theorem.
- `target_path_type_def` is adequate but should not be unfolded in the main proof. Existing boundary lemmas already express the needed consumer interface: `target_path_type_HashMapT_not_nil`, `target_path_type_HashMapT_split_hashmap_subscripts`, `target_path_type_HashMapT_hashmap_prefix_ValueSubscript`, `target_path_type_Type_place_leaf_typed`, and `place_leaf_path_typed_split_leaf_type`.
- `assign_operation_matches_target_shape_def` and `assign_target_assignable_def` are not needed for the BaseTargetV HashMapRef no-TypeError argument beyond being part of the strengthened upstream contract. Do not unfold them unless simplification introduces them.

### Probes

The material design probes are the helper components below: C3.1.1 packages static path facts, and C3.1.2 proves the evaluator branch boundary. If either helper is hard, the main theorem should not be attacked directly; re-plan the helper statement instead.

### Failure signs

If C3.1.1 cannot derive `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)`, then the path/split alignment is wrong and the proof will lack the key side condition for `assign_subscripts_no_type_error_runtime_typed`. If C3.1.2 leaves a persistent `compute_hashmap_slot = NONE` subgoal, the prefix list being fed to `compute_hashmap_slot_subscripts_to_values` is misaligned with the evaluator's `first_sub :: TAKE ... rest_subs`; fix that list alignment rather than unfolding more evaluator code.

## Code Structure

All edits stay in `semantics/prop/vyperTypeStatePreservationScript.sml` near the existing HashMap assignment helper lemmas and the cheated theorem. Do not move these helpers to a shared library unless later siblings independently require them. Preferred structure:

1. keep existing generic lemmas as-is;
2. add C3.1.1 immediately after `place_leaf_path_typed_split_leaf_type` or just before `top_level_HashMapRef_assign_no_type_error`;
3. add C3.1.2 immediately before `top_level_HashMapRef_assign_no_type_error`;
4. replace the theorem's `Proof cheat` with a short invocation proof.

## Components

### C3.1: Top-level HashMapRef assignment cannot return TypeError
- Statement: the user-provided `top_level_HashMapRef_assign_no_type_error` theorem.
- Approach: Reduce the declaration/layout hypotheses to a `lookup_global` HashMapRef result, package path/split/leaf facts, expand only the HashMapRef evaluator branch, and rule out each TypeError source using existing no-TypeError lemmas.
- Dependencies: C3.1.1, C3.1.2, C3.1.3
- Risk: 2
- Risk rationale: all mathematical ingredients already exist; only proof packaging and list alignment are non-mechanical.
- Checkpoint: yes
- Not to try: do not use `assign_target_sound_mutual` (circular) and do not inline the whole branch in the final theorem.

### C3.1.1: HashMap path facts package
- Kind: infrastructure lemma
- Dependencies: none
- Risk: 2
- Checkpoint: no
- Statement: `target_path_type_HashMapT_assign_facts` as specified in structured component C3.1.1.
- Approach: combine existing target-path and place-leaf lemmas; use `runtime_consistent` only to rewrite `env.type_defs = get_tenv cx`.
- Not to try: no fresh induction over `sbs`.

### C3.1.2: Successful HashMapRef assignment do-block has no TypeError
- Kind: boundary lemma
- Dependencies: C3.1.1
- Risk: 2
- Checkpoint: no
- Statement: `assign_target_HashMapRef_branch_no_type_error` as specified in structured component C3.1.2.
- Approach: expand `assign_target_def` once, rewrite lookup/module facts, use C3.1.1 and existing storage/assignment no-TypeError lemmas to discharge all TypeError cases.
- Not to try: avoid over-generalizing over arbitrary HashMapRef base slots unless necessary.

### C3.1.3: Public theorem proof
- Kind: proof
- Dependencies: C3.1.2
- Risk: 1
- Checkpoint: no
- Statement: exact theorem at lines ~2153-2166.
- Approach: derive the `lookup_global` HashMapRef equation with `lookup_global_HashMapVarDecl_returns_HashMapRef`, extract the successful split, and invoke C3.1.2.
- Not to try: do not unfold `assign_target_def` here.

## Dependency Graph

C3.1.1 → C3.1.2 → C3.1.3 → C3.1.

## Notes

This is an augment-only plan for dotted component `C3.1`, so `required_for_completion` is false in the structured metadata even though resolving this subtree is necessary for the parent assignment-target work. This subtree intentionally does not plan the sibling `ArrayRef`, `ImmutableVar`, `TupleTargetV`, or `assign_targets_cons` cheats. If the existing `sound_TopLevelVar` HashMapRef branch remains duplicated and cheated after this theorem is proved, the executor may replace that branch's local HashMapRef reasoning by an invocation of `top_level_HashMapRef_assign_no_type_error` only if it is already inside C3.1's ownership in the current plan; otherwise report back for a broader component update.

## Structured Components

### C3: C3
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.1 risk 2. All ingredients are already proved (`target_path_type_HashMapT_not_nil`, `target_path_type_HashMapT_split_hashmap_subscripts`, `target_path_type_HashMapT_hashmap_prefix_ValueSubscript`, `target_path_type_Type_place_leaf_typed`, and `place_leaf_path_typed_split_leaf_type`). This component only packages them with the exact `TL (REVERSE sbs)` path used by `assign_target_def`.
- Required for completion: yes

### C3.1: Top-level HashMapRef assignment cannot return TypeError
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The assignment evaluator branch is explicit in `assign_target_def`, and the needed ingredients already exist nearby: hashmap path splitting, hashmap prefix value-subscript facts, storage read error classification, storage read typedness, and `assign_subscripts_no_type_error_runtime_typed`. The remaining work is to package them so the main proof does not depend on fragile `gvs`-generated subgoals.
- Dependencies: C3.1.1, C3.1.2, C3.1.3
- Checkpoint: yes

#### Description
Owns only the standalone theorem `top_level_HashMapRef_assign_no_type_error` and strict helper lemmas needed for that theorem. Do not edit sibling assignment cases except to replace direct duplicated reasoning in the existing `sound_TopLevelVar` HashMapRef branch by an invocation of this theorem if the current source already calls for it.

#### Statement
```hol
runtime_consistent env cx st ==>
FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (HashMapT kt vt) ==>
target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
assignable_type (get_tenv cx) ty ==>
assign_operation_runtime_typed env ty op ==>
assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op ==>
assign_target_assignable (BaseTargetV (TopLevelVar src_id_opt id) sbs) st ==>
well_formed_vtype (get_tenv cx) (HashMapT kt vt) ==>
get_module_code cx src_id_opt = SOME code ==>
find_var_decl_by_num (string_to_num id) code = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
no_type_error_result res
```

#### Approach
First use `lookup_global_HashMapVarDecl_returns_HashMapRef` to rewrite the TopLevelVar evaluator to the `HashMapRef is_transient (n2w slot) kt vt` branch. `target_path_type_HashMapT_not_nil` supplies the mandatory first subscript. `target_path_type_HashMapT_split_hashmap_subscripts` supplies the successful split of the residual path, and `target_path_type_HashMapT_hashmap_prefix_ValueSubscript` plus `compute_hashmap_slot_subscripts_to_values` supplies successful slot computation. `place_leaf_path_typed_split_leaf_type` supplies the exact relationship between the type evaluated at the hashmap leaf (`final_tv`) and the assignment leaf type (`ty`), which is the key input to `assign_subscripts_no_type_error_runtime_typed`. Then prove the TypeError contradiction by expanding only the HashMapRef do-block and discharging each possible TypeError source: impossible option failures by the success facts, `read_storage_slot` by `read_storage_slot_error`, `assign_subscripts` by `assign_subscripts_no_type_error_runtime_typed`, optional `write_storage_slot` by typed writes if it appears, and final `assign_result` by `assign_result_no_type_error_from_successful_assign`.

#### Not to try
Do not continue the current inlined proof style after line ~2248 by manually chasing generated names (`x'`, `xs`, etc.) across `gvs[bind_def,...]`; it is brittle and already left a cheat. Do not unfold `target_path_type_def` recursively in the main theorem. Do not use `assign_target_sound_mutual` to prove this theorem; this theorem is intended to discharge the HashMapRef branch of that mutual proof, so that would be circular.

### C3.1.1: HashMap path facts package
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: All ingredients are already proved (`target_path_type_HashMapT_not_nil`, `target_path_type_HashMapT_split_hashmap_subscripts`, `target_path_type_HashMapT_hashmap_prefix_ValueSubscript`, `target_path_type_Type_place_leaf_typed`, and `place_leaf_path_typed_split_leaf_type`). This component only packages them with the exact `TL (REVERSE sbs)` path used by `assign_target_def`.

#### Description
Add a local theorem near the existing HashMap helper lemmas in `vyperTypeStatePreservationScript.sml`. This is a strict helper for C3.1; keep it in this file rather than moving to a library.

#### Statement
Recommended statement:
```hol
Theorem target_path_type_HashMapT_assign_facts:
  runtime_consistent env cx st /\
  well_formed_vtype (get_tenv cx) (HashMapT kt vt) /\
  target_path_type env (HashMapT kt vt) sbs (Type ty) /\
  split_hashmap_subscripts vt (TL (REVERSE sbs)) = SOME (final_type,kts,remaining) ==>
  sbs <> [] /\
  EVERY ((<>) NONE o subscript_to_value)
    (LAST sbs :: TAKE (LENGTH kts) (TL (REVERSE sbs))) /\
  ?final_tv.
    evaluate_type (get_tenv cx) final_type = SOME final_tv /\
    evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)
```
If `runtime_consistent` rewriting is inconvenient, replace it by the smaller hypothesis `env.type_defs = get_tenv cx`; derive that equality in C3.1 from `runtime_consistent_def, env_consistent_def, env_context_consistent_def`.

#### Approach
Use `runtime_consistent` only to rewrite `env.type_defs = get_tenv cx`. The non-empty and prefix-subscript conjuncts are direct applications of the existing target-path HashMap lemmas. For the existential `final_tv`, derive `?pl_tv. place_leaf_typed env (HashMapT kt vt) sbs ty pl_tv` from `target_path_type_Type_place_leaf_typed`; unfold `place_leaf_typed_def`, use `sbs <> []` to rewrite `REVERSE sbs` as first element plus tail, simplify `place_leaf_path_typed_def` once, and apply `place_leaf_path_typed_split_leaf_type` to `vt` and `TL (REVERSE sbs)`.

#### Not to try
Do not prove this by induction over `sbs`; the repository already has the needed induction results. Do not require facts about actual runtime key values beyond `subscript_to_value <> NONE`, because `compute_hashmap_slot` only needs syntactic conversion of subscripts to values.

### C3.1.2: Successful HashMapRef assignment do-block has no TypeError
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: This isolates the evaluator expansion from the public theorem. The proof is a straight case analysis on the `do` block once C3.1.1 provides successful option computations and leaf typing. Remaining TypeError sources are handled by existing `read_storage_slot_error`, `read_storage_slot_well_typed_value`, and `assign_subscripts_no_type_error_runtime_typed`.
- Dependencies: C3.1.1

#### Description
Add a lemma specifically for the `HashMapRef` arm of `assign_target_def`. It should be phrased in terms of `split_hashmap_subscripts`, `compute_hashmap_slot`, and the final `assign_target ... = (res,st')` equation so that C3.1 itself does not need to inspect every bind-generated subcase.

#### Statement
Recommended statement:
```hol
Theorem assign_target_HashMapRef_branch_no_type_error:
  runtime_consistent env cx st /\
  well_formed_vtype (get_tenv cx) (HashMapT kt vt) /\
  target_path_type env (HashMapT kt vt) sbs (Type ty) /\
  assignable_type (get_tenv cx) ty /\
  assign_operation_runtime_typed env ty op /\
  split_hashmap_subscripts vt (TL (REVERSE sbs)) = SOME (final_type,kts,remaining) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (res,st') /\
  lookup_global cx src (string_to_num id) st =
    (INL (HashMapRef is_transient (n2w slot) kt vt), st) /\
  get_module_code cx src = SOME code ==>
  no_type_error_result res
```
If direct use of `assign_target_def` still needs the declaration/layout hypotheses to simplify `lookup_global`, either keep the `lookup_global ... = ...` hypothesis and rewrite before unfolding, or include the original `find_var_decl_by_num`/`lookup_var_slot_from_layout` hypotheses and use `lookup_global_HashMapVarDecl_returns_HashMapRef` inside the lemma.

#### Approach
Obtain `sbs <> []`, prefix value-subscript facts, and the `final_tv`/leaf relation from C3.1.1. From `split_hashmap_subscripts_some_imp`, prove `LENGTH kts <= LENGTH (TL (REVERSE sbs))`; with the prefix fact, apply `compute_hashmap_slot_subscripts_to_values` to show slot computation is not `NONE`. Use `HD_REVERSE_EQ_LAST` and `TL_REVERSE_eq_REVERSE_FRONT` only to align the evaluator's `first_sub :: TAKE ... rest_subs` with `LAST sbs :: TAKE ... (TL (REVERSE sbs))` after the evaluator splits `REVERSE sbs` into `first_sub::rest_subs`. Expand `assign_target_def` once for the TopLevelVar case, rewrite the assumed successful `lookup_global` and `get_module_code`, and simplify `lift_option_type`/`bind` enough to expose the HashMapRef branch. For a hypothetical `res = INR (Error (TypeError msg))`, discharge sources as follows: empty-subscript and split/slot/evaluate-type failures contradict the facts above; `read_storage_slot` cannot TypeError by `read_storage_slot_error`; if the read succeeds, `read_storage_slot_well_typed_value` gives `value_has_type final_tv current_val`; `evaluate_type_well_formed_type_value` gives `well_formed_type_value final_tv`; `assignable_type_evaluate_not_NoneTV` and `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)` give the non-`NoneTV` leaf side condition; then `assign_subscripts_no_type_error_runtime_typed` rules out TypeError from `assign_subscripts`. If execution reaches `assign_result`, use `assign_result_no_type_error_from_successful_assign`.

#### Not to try
Do not add a general theorem about all `HashMapRef` assignments over arbitrary `base_slot` unless this exact statement is too weak; generality tends to introduce word/slot alignment clutter. Do not try to prove write-storage no TypeError unless the branch actually leaves a `write_storage_slot` TypeError subgoal; if it does, use `write_storage_slot_no_type_error_from_value_has_type` after deriving typedness of the new value.

### C3.1.3: Prove the public standalone theorem by reduction to the HashMapRef branch lemma
- Kind: `proof`
- Risk: 1
- Rationale: After C3.1.2, the top-level theorem is just bookkeeping: convert the declaration/layout hypotheses into the `lookup_global` HashMapRef equation and invoke the branch lemma.
- Dependencies: C3.1.2

#### Description
Replace `Proof cheat` for `top_level_HashMapRef_assign_no_type_error` in `vyperTypeStatePreservationScript.sml`.

#### Statement
Same as the user-provided theorem/source theorem at lines ~2153-2166.

#### Approach
From `get_module_code`, `find_var_decl_by_num`, and `lookup_var_slot_from_layout`, use `lookup_global_HashMapVarDecl_returns_HashMapRef` to obtain `lookup_global cx src_id_opt (string_to_num id) st = (INL (HashMapRef is_transient (n2w slot) kt vt), st)`. From `target_path_type_HashMapT_split_hashmap_subscripts` and `well_formed_vtype (get_tenv cx) (HashMapT kt vt)`, get an existential `split_hashmap_subscripts vt (TL (REVERSE sbs)) = SOME (...)`; extract its components and invoke C3.1.2. `assign_operation_matches_target_shape` and `assign_target_assignable` are hypotheses of the theorem but irrelevant for this BaseTargetV/HashMapRef no-TypeError proof; leave them unused unless simplification requires them.

#### Not to try
Do not unfold `assign_target_def` again here; that duplicates C3.1.2. Do not attempt to derive assignability context from the standalone theorem's weaker `assign_target_assignable`; context was deliberately expanded into explicit module/declaration/layout hypotheses.

---

## PLAN AUGMENT: C3.1 @ 2026-05-14T03:24:25+00:00

# PLAN: C3.1 — prove top-level HashMapRef assignment no-TypeError

## Argument

A top-level variable declared as `HashMapVarDecl is_transient kt vt` is evaluated by `lookup_global` to `HashMapRef is_transient (n2w slot) kt vt` when the module code and layout slot are present. Assignment to a HashMapRef is only valid through at least one subscript. The static target path

```sml
target_path_type env (HashMapT kt vt) sbs (Type ty)
```

therefore implies `sbs <> []`. Since `assign_target` works with `REVERSE sbs`, the first runtime subscript is `LAST sbs`, and the remaining runtime path is `TL (REVERSE sbs)`. Splitting that remaining path through nested hashmaps yields

```sml
split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,remaining)
```

where the consumed hashmap prefix is exactly `TAKE (LENGTH kts) rest_subs`, and the leftover path `remaining` is the ordinary in-slot subscript path for the value stored at the computed hashmap slot.

The target-path typing gives two critical safety facts. First, every subscript in the hashmap-key prefix has `subscript_to_value <> NONE`, so `compute_hashmap_slot` cannot fail. Second, the `place_leaf`/split lemmas connect the final storage type to the assignment leaf:

```sml
evaluate_type env.type_defs final_type = SOME final_tv
/\
evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)
```

and `assignable_type ty` excludes `NoneTV` at that leaf. Thus `read_storage_slot` does not raise a TypeError, `assign_subscripts` does not raise a TypeError under `assign_operation_runtime_typed`, any successful assigned value remains typed for `final_tv`, `write_storage_slot` cannot TypeError because encoding a well-typed value succeeds, and `assign_result` cannot TypeError after a successful `assign_subscripts`.

## Definition Design

No new definitions are needed. The existing definitions have the right proof interface:

- `assign_target_def` is the operational boundary. It should be unfolded once in the final proof after all path/split/typing facts are available.
- `target_path_type_def` is intentionally reverse-recursive relative to concrete evaluation order. Consumers should not unfold it directly; use existing HashMap lemmas such as `target_path_type_HashMapT_not_nil`, `target_path_type_HashMapT_split_hashmap_subscripts`, and `target_path_type_HashMapT_hashmap_prefix_ValueSubscript`.
- `place_leaf_typed_def` and `place_leaf_path_typed_def` bridge target-path typing to `leaf_type`; consumers should use `target_path_type_Type_place_leaf_typed` and `place_leaf_path_typed_split_leaf_type` instead of unfolding recursively.
- `assign_operation_runtime_typed_def` should stay behind boundary lemmas (`assign_subscripts_no_type_error_runtime_typed`, `assign_subscripts_preserves_type_runtime_typed`, `assign_result_no_type_error_from_successful_assign`).

Probes/boundary checks are C3.1.2–C3.1.5. Failure signs would be: inability to derive `split_hashmap_subscripts vt (TL (REVERSE sbs)) <> NONE` from the target path, inability to prove hashmap prefix subscripts have `subscript_to_value`, or inability to connect `final_type` to `leaf_type final_tv remaining`. The gathered source already contains lemmas for all three, so no redesign is expected.

## Code Structure

Work only in `semantics/prop/vyperTypeStatePreservationScript.sml`, near the existing cheated theorem and its nearby HashMap helper lemmas. Add the small helper theorems immediately before `top_level_HashMapRef_assign_no_type_error`, because they are local to this assignment-preservation proof layer. Do not move definitions or create library files.

After proving the theorem, optionally replace only the HashMapRef sub-branch in `Resume assign_target_sound_mutual[sound_TopLevelVar]` with a call to this theorem. Do not edit sibling unfinished branches (`ArrayRef`, `ImmutableVar`, `TupleTargetV`, `assign_targets_cons`) under this augment request.

## Components

### C3.1: Top-level HashMapRef assignment cannot return TypeError
- Statement: the task theorem `top_level_HashMapRef_assign_no_type_error` exactly as given.
- Approach: prove small path/split/storage wrappers first, then perform a single controlled unfold of `assign_target_def` and discharge each TypeError branch by contradiction.
- Dependencies: C3.1.1–C3.1.6; C3.1.7 for optional in-subtree integration.
- Risk: 2
- Checkpoint: yes
- Not to try: do not use `assign_target_sound_mutual` to prove this helper; that would be circular.

### C3.1.1: Normalize the top-level HashMap lookup branch
Use existing `lookup_global_HashMapVarDecl_returns_HashMapRef`.

### C3.1.2: HashMap path decomposition facts for assign_target's reversed path
Prove `target_path_type_HashMapT_assign_target_decomp`, packaging `REVERSE sbs = first_sub::rest_subs`, split success, split length, and prefix subscript encodability.

### C3.1.3: HashMap assignment leaf typing facts after split
Prove `target_path_type_HashMapT_split_leaf_runtime`, packaging final type evaluation, leaf evaluation, non-`NoneTV`, and `well_formed_type_value`.

### C3.1.4: HashMap compute slot succeeds from typed prefix
Prove `compute_hashmap_slot_assign_target_prefix_some` by `compute_hashmap_slot_subscripts_to_values` and arithmetic.

### C3.1.5: Storage read/assign/write/assign_result TypeError exclusions for HashMap leaf
Prove local wrappers around `assign_subscripts_no_type_error_runtime_typed`, `assign_subscripts_preserves_type_runtime_typed`, `write_storage_slot_no_type_error_from_value_has_type`, and use `assign_result_no_type_error_from_successful_assign` directly.

### C3.1.6: Main theorem proof
Use C3.1.1–C3.1.5 to replace `Proof cheat` of `top_level_HashMapRef_assign_no_type_error`.

### C3.1.7: Integrate helper into sound_TopLevelVar HashMapRef branch
If this branch is part of C3.1 in the current plan, replace only the HashMapRef branch script/cheat with a call to the proved theorem.

## Dependency Graph

C3.1.1 is independent. C3.1.2 is independent. C3.1.3 depends on the split shape from C3.1.2. C3.1.4 depends on C3.1.2. C3.1.5 depends on C3.1.3. C3.1.6 depends on C3.1.1–C3.1.5. C3.1.7 depends on C3.1.6.

## Notes

- This is an augment plan for dotted component `C3.1`; schema-required `required_for_completion` is left false because only top-level component IDs may set it. Semantically, C3.1 remains the requested subtree obligation.
- The theorem statement does not need `assign_target_assignable_context`; it has the stronger concrete module-code/declaration/slot premises directly. `assign_target_assignable` is irrelevant for TopLevelVar except as a harmless premise.
- `assign_operation_matches_target_shape` is trivial for `BaseTargetV` by definition and should not drive the proof.
- If C3.1.3 fails because `place_leaf_path_typed_split_leaf_type` expects the exact tail path, keep the explicit `rest_subs = TL (REVERSE sbs)` premise as written and use C3.1.2's equality. This would not invalidate sibling components.
- If the storage wrapper in C3.1.5 is syntactically too large, keep it split into the two recommended lemmas; do not broaden scope.

## Structured Components

### C3: C3
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.2 risk 2. The needed facts are direct combinations of already-proved lemmas (`target_path_type_HashMapT_not_nil`, `target_path_type_HashMapT_split_hashmap_subscripts`, `target_path_type_HashMapT_hashmap_prefix_ValueSubscript`, `HD_REVERSE_EQ_LAST`, `split_hashmap_subscripts_some_imp`) and list arithmetic. This isolates the brittle list orientation in one place.
- Required for completion: yes

### C3.1: Top-level HashMapRef assignment cannot return TypeError
- Kind: `proof_cluster`
- Risk: 2
- Rationale: The source already contains nearly all structural lemmas needed for the HashMapRef branch: split success from target_path_type, hashmap-prefix subscript encodability, split-to-leaf typing, assignment-subscript no-TypeError/preservation, read/write storage no-TypeError. The remaining work is integration and small boundary lemmas to avoid brittle do-block case reasoning.
- Checkpoint: yes

#### Description
Prove the task theorem `top_level_HashMapRef_assign_no_type_error` in `vyperTypeStatePreservationScript.sml`, and use it to replace the remaining cheated HashMapRef branch inside `Resume assign_target_sound_mutual[sound_TopLevelVar]` only if this branch is within the existing C3.1 subtree. Do not touch ArrayRef/Immutable/Tuple/assign_targets sibling cheats.

#### Statement
```sml
Theorem top_level_HashMapRef_assign_no_type_error:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (HashMapT kt vt) ==>
  target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
  assignable_type (get_tenv cx) ty ==>
  assign_operation_runtime_typed env ty op ==>
  assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op ==>
  assign_target_assignable (BaseTargetV (TopLevelVar src_id_opt id) sbs) st ==>
  well_formed_vtype (get_tenv cx) (HashMapT kt vt) ==>
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num (string_to_num id) code = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```

#### Approach
Open `assign_target_def` only once after deriving all semantic facts about the path. Use `lookup_global_HashMapVarDecl_returns_HashMapRef` to normalize the lookup branch. From `target_path_type env (HashMapT kt vt) sbs (Type ty)`, prove `sbs <> []`; decompose `REVERSE sbs = first_sub::rest_subs` with `first_sub = LAST sbs` and `rest_subs = TL (REVERSE sbs)`. Use `target_path_type_HashMapT_split_hashmap_subscripts` to obtain `split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,remaining)`. Use `target_path_type_HashMapT_hashmap_prefix_ValueSubscript` plus `compute_hashmap_slot_subscripts_to_values` to show `compute_hashmap_slot (n2w slot) (kt::kts) (first_sub::TAKE (LENGTH kts) rest_subs) <> NONE`. Use `place_leaf_path_typed_split_leaf_type` to derive `evaluate_type env.type_defs final_type = SOME final_tv`, `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)`, and then transfer to `get_tenv cx` via `runtime_consistent`/`env_context_consistent`. Then case-analyse the monadic computation: option-lift TypeError branches contradict split/evaluate/slot facts, `read_storage_slot` TypeError contradicts `read_storage_slot_error`, `assign_subscripts` TypeError contradicts `assign_subscripts_no_type_error_runtime_typed`, `write_storage_slot` TypeError contradicts typedness of the new value, and successful `assign_result` is discharged by `assign_result_no_type_error_from_successful_assign`.

#### Not to try
Do not try to prove the theorem by using the full mutual theorem `assign_target_sound_mutual`; this theorem is a helper needed for that mutual proof and would create a dependency cycle. Do not unfold `target_path_type_def` throughout the final proof; use the existing HashMap-specific path lemmas. Do not rely on `gvs[assign_target_def]` before deriving split/compute/evaluate facts; it produces many fragile case subgoals with hidden equalities.

### C3.1.1: Normalize the top-level HashMap lookup branch
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: This lemma is already present as `lookup_global_HashMapVarDecl_returns_HashMapRef`; at most the executor must reuse it, not invent a proof.

#### Description
Use the existing lemma to rewrite `lookup_global` at the beginning of the HashMapRef proof.

#### Statement
Existing theorem:
```sml
Theorem lookup_global_HashMapVarDecl_returns_HashMapRef:
  get_module_code cx src = SOME code ==>
  find_var_decl_by_num n code = SOME (HashMapVarDecl is_t kt vt, id) ==>
  lookup_var_slot_from_layout cx is_t src id = SOME slot ==>
  lookup_global cx src n st = (INL (HashMapRef is_t (n2w slot) kt vt), st)
```

#### Approach
Instantiate with `src_id_opt`, `string_to_num id`, `is_transient`, `kt`, `vt`, `id_str`, and `slot`. This should make the initial `lookup_global` bind in `assign_target_def` reduce to the HashMapRef case and also gives the state after lookup as exactly `st`.

#### Not to try
Do not re-prove this by unfolding `lookup_global_def` inside the main theorem unless rewriting with the existing theorem fails syntactically.

### C3.1.2: HashMap path decomposition facts for assign_target's reversed path
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: The needed facts are direct combinations of already-proved lemmas (`target_path_type_HashMapT_not_nil`, `target_path_type_HashMapT_split_hashmap_subscripts`, `target_path_type_HashMapT_hashmap_prefix_ValueSubscript`, `HD_REVERSE_EQ_LAST`, `split_hashmap_subscripts_some_imp`) and list arithmetic. This isolates the brittle list orientation in one place.

#### Description
Add one local helper immediately before `top_level_HashMapRef_assign_no_type_error` that packages the facts needed by the monadic proof.

#### Statement
Recommended helper statement:
```sml
Theorem target_path_type_HashMapT_assign_target_decomp:
  well_formed_vtype env.type_defs (HashMapT kt vt) /\
  target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
  ?first_sub rest_subs final_type kts remaining.
    REVERSE sbs = first_sub :: rest_subs /\
    first_sub = LAST sbs /\
    rest_subs = TL (REVERSE sbs) /\
    split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,remaining) /\
    LENGTH kts + LENGTH remaining = LENGTH rest_subs /\
    EVERY ((<>) NONE o subscript_to_value)
      (first_sub :: TAKE (LENGTH kts) rest_subs)
```

#### Approach
First derive `sbs <> []` via `target_path_type_HashMapT_not_nil`, then case on `REVERSE sbs` to obtain `first_sub::rest_subs`; use `HD_REVERSE_EQ_LAST` to identify `first_sub = LAST sbs` and simplification for `rest_subs = TL (REVERSE sbs)`. Get split success via `target_path_type_HashMapT_split_hashmap_subscripts` and choose its triple using `optionTheory.IS_SOME_EXISTS`. Length comes from `split_hashmap_subscripts_some_imp`. The `EVERY` fact is exactly `target_path_type_HashMapT_hashmap_prefix_ValueSubscript` after rewriting `first_sub`/`rest_subs`.

#### Not to try
Do not destruct `sbs` from the front and then reason about `LAST` by hand; `assign_target` consumes `REVERSE sbs`, so the stable decomposition is by `REVERSE sbs = first_sub::rest_subs`.

### C3.1.3: HashMap assignment leaf typing facts after split
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: This is a thin wrapper around `target_path_type_Type_place_leaf_typed` and `place_leaf_path_typed_split_leaf_type`, with an environment equality from `runtime_consistent`. It prevents the main proof from having to unfold `place_leaf_typed_def` repeatedly.
- Dependencies: C3.1.2

#### Description
Prove a helper that turns the target path and split result into the exact `evaluate_type` and non-`NoneTV` facts required by `assign_subscripts_no_type_error_runtime_typed`.

#### Statement
Recommended helper statement:
```sml
Theorem target_path_type_HashMapT_split_leaf_runtime:
  runtime_consistent env cx st /\
  well_formed_vtype (get_tenv cx) (HashMapT kt vt) /\
  target_path_type env (HashMapT kt vt) sbs (Type ty) /\
  rest_subs = TL (REVERSE sbs) /\
  split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,remaining) /\
  assignable_type (get_tenv cx) ty ==>
  ?final_tv.
    evaluate_type (get_tenv cx) final_type = SOME final_tv /\
    evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) /\
    leaf_type final_tv remaining <> NoneTV /\
    well_formed_type_value final_tv
```

#### Approach
From `runtime_consistent_def`, `env_consistent_def`, and `env_context_consistent_def`, derive `env.type_defs = get_tenv cx`. Rewrite the well-formed hypothesis to `env.type_defs`. Use `target_path_type_Type_place_leaf_typed` to get `place_leaf_typed env (HashMapT kt vt) sbs ty final_leaf_tv`; unfold `place_leaf_typed_def`, rewrite `rest_subs = TL (REVERSE sbs)`, and use `place_leaf_path_typed_split_leaf_type` with the split assumption to obtain `evaluate_type env.type_defs final_type = SOME final_tv` and `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)`. The `leaf_type ... <> NoneTV` fact follows from `assignable_type_evaluate_not_NoneTV`; `well_formed_type_value final_tv` follows from `evaluate_type_well_formed_type_value`.

#### Not to try
Do not attempt to prove `evaluate_type (get_tenv cx) ty = SOME ...` by induction on `target_path_type`; the existing `place_leaf` lemmas already encode the reversed path convention correctly.

### C3.1.4: HashMap compute slot succeeds from typed prefix
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: This is a direct application of `compute_hashmap_slot_subscripts_to_values`; only list length arithmetic is involved.
- Dependencies: C3.1.2

#### Description
Package the compute-slot success fact in the form matching `assign_target_def`.

#### Statement
Recommended helper statement:
```sml
Theorem compute_hashmap_slot_assign_target_prefix_some:
  LENGTH kts + LENGTH remaining = LENGTH rest_subs /\
  EVERY ((<>) NONE o subscript_to_value)
    (first_sub :: TAKE (LENGTH kts) rest_subs) ==>
  compute_hashmap_slot base_slot (kt::kts)
    (first_sub :: TAKE (LENGTH kts) rest_subs) <> NONE
```

#### Approach
Use `compute_hashmap_slot_subscripts_to_values`. The length side condition is `LENGTH (kt::kts) = LENGTH (first_sub::TAKE (LENGTH kts) rest_subs)`, which follows from `LENGTH kts <= LENGTH rest_subs`; derive that by arithmetic from `LENGTH kts + LENGTH remaining = LENGTH rest_subs`, then simplify `LENGTH_TAKE_EQ`.

#### Not to try
Do not reason about `compute_hashmap_slot_def` recursively in the main theorem; it is unnecessary and will expose key encoding details.

### C3.1.5: Storage read/assign/write/assign_result TypeError exclusions for HashMap leaf
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: All required facts already exist, but the main theorem benefits from local wrappers matching the monadic sequence. The only nontrivial point is preserving type of `new_val`, handled by `assign_subscripts_preserves_type_runtime_typed`.
- Dependencies: C3.1.3

#### Description
Add small wrapper lemmas for the storage-leaf part of the HashMapRef case. They should not mention HashMap paths or slots beyond the already-computed `final_slot` and `final_tv`.

#### Statement
Recommended helper statements:
```sml
Theorem hashmap_leaf_assign_subscripts_no_type_error:
  value_has_type final_tv current_val /\
  well_formed_type_value final_tv /\
  leaf_type final_tv remaining <> NoneTV /\
  assign_operation_runtime_typed env ty op /\
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) ==>
  assign_subscripts final_tv current_val remaining op <> INR (TypeError msg)

Theorem hashmap_leaf_write_no_type_error_after_assign:
  assign_subscripts final_tv current_val remaining op = INL new_val /\
  value_has_type final_tv current_val /\
  well_formed_type_value final_tv /\
  assign_operation_runtime_typed env ty op /\
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) ==>
  write_storage_slot cx is_transient final_slot final_tv new_val st_read <>
    (INR (Error (TypeError msg)), st_write)
```
Use existing `assign_result_no_type_error_from_successful_assign` directly for final `assign_result`.

#### Approach
For current value typing in the main proof, use `read_storage_slot_well_typed_value`. The first helper is exactly `assign_subscripts_no_type_error_runtime_typed`. The second helper first applies `assign_subscripts_preserves_type_runtime_typed` to get `value_has_type final_tv new_val`, then uses `write_storage_slot_no_type_error_from_value_has_type`. For the final result, apply `assign_result_no_type_error_from_successful_assign` to the successful `assign_subscripts` equality and the `assign_result` equality.

#### Not to try
Do not use `write_storage_slot_preserves_*` preservation lemmas here; this theorem only needs absence of TypeError in the result, and preservation is handled elsewhere.

### C3.1.6: Main proof of top_level_HashMapRef_assign_no_type_error
- Kind: `proof`
- Risk: 2
- Rationale: After helpers, the main proof is deterministic monadic case analysis over `assign_target_def`. Each possible TypeError branch is contradicted by a pre-derived helper fact; successful final result is discharged by `assign_result_no_type_error_from_successful_assign`.
- Dependencies: C3.1.1, C3.1.2, C3.1.3, C3.1.4, C3.1.5
- Checkpoint: yes

#### Description
Replace `Proof cheat` of `top_level_HashMapRef_assign_no_type_error`.

#### Statement
Same as C3.1 top-level theorem.

#### Approach
1. Strip assumptions. Derive `env.type_defs = get_tenv cx` from `runtime_consistent` for rewriting helper statements.
2. Apply C3.1.2 to obtain `REVERSE sbs = first_sub::rest_subs`, split triple, length, and prefix-subscript facts.
3. Apply C3.1.4 to get `compute_hashmap_slot (n2w slot) (kt::kts) (first_sub::TAKE (LENGTH kts) rest_subs) <> NONE`.
4. Apply C3.1.3 to get `final_tv`, `evaluate_type (get_tenv cx) final_type = SOME final_tv`, `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)`, `leaf_type ... <> NoneTV`, and `well_formed_type_value final_tv`.
5. Use C3.1.1 and unfold `assign_target_def` once. Rewrite lookup, module code, split, compute-slot-not-NONE, and evaluate-type facts. If the concrete term uses `LENGTH rest_subs - LENGTH remaining` instead of `LENGTH kts`, prove `LENGTH rest_subs - LENGTH remaining = LENGTH kts` from `LENGTH kts + LENGTH remaining = LENGTH rest_subs` before simplifying `TAKE`.
6. For a `read_storage_slot` TypeError branch, use `read_storage_slot_error`; for an `assign_subscripts` TypeError branch, use `hashmap_leaf_assign_subscripts_no_type_error` after deriving current value typed via `read_storage_slot_well_typed_value`; for a `write_storage_slot` TypeError branch, use `hashmap_leaf_write_no_type_error_after_assign`; for the final `assign_result`, use `assign_result_no_type_error_from_successful_assign`.
7. Finish by rewriting `no_type_error_result_def` only at the final contradictions, not globally at the beginning.

#### Not to try
Do not case split on `tv` from `lookup_global`; C3.1.1 has already forced the `HashMapRef` branch. Do not leave arithmetic about `LENGTH rest_subs - LENGTH remaining` inside the `gvs[assign_target_def]` step; prove the equality to `LENGTH kts` first.

### C3.1.7: Integrate helper into sound_TopLevelVar HashMapRef branch
- Kind: `integration`
- Risk: 2
- Rationale: The existing `sound_TopLevelVar` proof already isolates the HashMapRef branch and derives the needed declaration/path/context facts. Replacing its internal handwritten HashMap proof with a call to the proved theorem should be standard, but variable names may need small adaptation.
- Dependencies: C3.1.6

#### Description
If C3.1 scope includes the existing HashMapRef branch of `Resume assign_target_sound_mutual[sound_TopLevelVar]`, replace only that branch's cheat/partial script with an invocation of `top_level_HashMapRef_assign_no_type_error`.

#### Statement
No new theorem statement. The integration proves the HashMapRef subgoal in:
```sml
Resume assign_target_sound_mutual[sound_TopLevelVar]: ...
```

#### Approach
In the branch where `lookup_global`/`tv` is `HashMapRef`, derive the theorem premises from the mutual branch assumptions: runtime consistency and operation typing are direct; `FLOOKUP ... = SOME (HashMapT kt vt)` comes from `target_runtime_typed_def`/`location_runtime_typed_def`; `target_path_type` is already present after destructing `target_runtime_typed`; `assignable_type`, shape, and assignable context come from the strengthened mutual assumptions; from `assign_target_assignable_context_def` obtain `get_module_code`, `find_var_decl_by_num`, and slot existence, and align constructor parameters using `lookup_global_HashMapVarDecl_returns_HashMapRef` or the already-present lookup equality. Then call `top_level_HashMapRef_assign_no_type_error` for the `no_type_error_result` conjunct; preserve the runtime-consistency conjunct by the already-proved `assign_target_preserves_state_well_typed_mutual`.

#### Not to try
Do not re-open the full HashMap monadic proof inside `sound_TopLevelVar`; that duplication caused the previous brittle failure. Do not modify ArrayRef or other unfinished branches.

---

## PLAN AUGMENT: C3.1.6 @ 2026-05-14T04:33:16+00:00

# PLAN: C3.1.6 — prove `top_level_HashMapRef_assign_no_type_error`

## Argument

A top-level variable declared as `HashMapVarDecl is_transient kt vt` is never materialised as a storage `Value`; `lookup_global` returns a `HashMapRef is_transient (n2w slot) kt vt`. Assignment to such a target is therefore the `HashMapRef` branch of `assign_target_def`.

The static `target_path_type env (HashMapT kt vt) sbs (Type ty)` supplies exactly the dynamic facts that this branch needs. Since a HashMap assignment must include at least one subscript, `REVERSE sbs` decomposes into the first key subscript and the rest. The rest splits through nested HashMaps into `(final_type, key_types, remaining_subs)`. The prefix of key subscripts is value-shaped, so `compute_hashmap_slot` succeeds. The final storage type evaluates to some `final_tv`, and the assignment leaf type `ty` evaluates to `leaf_type final_tv remaining_subs`, which is not `NoneTV` because `ty` is assignable.

After these facts are established, the operational proof is a linear monadic branch argument. All option lookups in the `HashMapRef` do-block succeed. `read_storage_slot` cannot return a TypeError; on success it returns a value of `final_tv`. `assign_subscripts` cannot return a TypeError because the current value has type `final_tv`, the leaf type is non-`NoneTV`, and the operation is runtime-typed for `ty`. If `assign_subscripts` succeeds, it preserves `value_has_type final_tv`, so `write_storage_slot` cannot return a TypeError, and `assign_result` after a successful assignment also cannot return a TypeError. Other non-TypeError errors are allowed by `no_type_error_result`.

## Definition Design

No new definitions are needed.

Existing definitions are adequate:

- `assign_target_def`
  - Purpose: operational assignment semantics.
  - Shape: pattern recursion over target value; the relevant branch is `BaseTargetV (TopLevelVar _ _)` followed by a case on `lookup_global` result.
  - Boundary: consume `lookup_global_HashMapVarDecl_returns_HashMapRef`, path decomposition lemmas, and storage/assign no-TypeError lemmas instead of unfolding unrelated branches.
  - Probe: after deriving `lookup_global = INL (HashMapRef ...)`, one `Once assign_target_def` should reduce to the HashMapRef do-block.
  - Failure signs: if simplification explores `Value`, `ArrayRef`, scoped, immutable, or tuple branches, the proof unfolded too early or lost the lookup fact.

- `target_path_type` / `place_leaf_typed`
  - Purpose: static typing of assignment paths.
  - Shape: consumers should use decomposition lemmas, not unfold recursive internals.
  - Boundary: C3.1.6.2 and C3.1.6.3.
  - Probe: derive `REVERSE sbs = first_sub::rest_subs` and `split_hashmap_subscripts vt rest_subs = SOME ...` before unfolding `assign_target`.
  - Failure signs: induction on `sbs` in the main theorem or direct case analysis on `target_path_type` means the abstraction boundary is being bypassed.

- `assign_operation_runtime_typed`
  - Purpose: dynamic typing contract for replace/update/append/pop assignment operations.
  - Boundary: use `assign_subscripts_no_type_error_runtime_typed` and `assign_subscripts_preserves_type_runtime_typed`.
  - Probe: once `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)` is available, these lemmas should apply without inspecting operation constructors.
  - Failure signs: case splitting on `op` in this theorem; that belongs in the lower-level assign-subscript lemmas.

`assign_operation_matches_target_shape` and `assign_target_assignable` are intentionally not unfolded here: for a `BaseTargetV`, shape is trivial, and top-level assignability imposes no extra runtime condition. They are present because the mutual soundness theorem has a uniform strengthened interface.

## Code Structure

Work in `semantics/prop/vyperTypeStatePreservationScript.sml` near the existing HashMap assignment helper region, immediately before `Resume assign_target_sound_mutual[sound_TopLevelVar]`.

Keep helper lemmas local to this theory; do not move them to `*Lib.sml` and do not change evaluator definitions. The preferred organization is:

1. Operational lookup boundary: `lookup_global_HashMapVarDecl_returns_HashMapRef` (already present in current source).
2. Static path decomposition: `target_path_type_HashMapT_assign_target_decomp` and `target_path_type_HashMapT_split_leaf_runtime` (already present in current source).
3. Optional integration helper `assign_target_HashMapRef_branch_no_type_error` if the inline proof of the main theorem remains brittle.
4. Main theorem `top_level_HashMapRef_assign_no_type_error`.

The executor may reuse existing proved lemmas rather than recreating them. If current source already contains C3.1.6.1–C3.1.6.3 with these names, treat those subcomponents as complete and focus on C3.1.6.4/C3.1.6.

## Components

### C3.1.6: Top-level HashMapRef assignment cannot produce TypeError
- Statement: the exact theorem from the task, `top_level_HashMapRef_assign_no_type_error`.
- Approach: derive lookup, path split, slot success, and final leaf runtime facts first; then unfold only the `TopLevelVar`/`HashMapRef` assign branch and eliminate TypeError-producing subcalls with storage and assign-subscript boundary lemmas.
- Dependencies: C3.1.6.1, C3.1.6.2, C3.1.6.3, C3.1.6.4
- Risk: 2
- Checkpoint: no
- Not to try: do not expand recursive path typing or case split on `op` in this theorem.

### C3.1.6.1: HashMap declaration lookup gives a HashMapRef global value
- Statement: `lookup_global_HashMapVarDecl_returns_HashMapRef` as above.
- Approach: direct unfolding of `lookup_global_def`.
- Dependencies: none
- Risk: 1
- Checkpoint: no
- Not to try: do not use runtime consistency; it is not needed.

### C3.1.6.2: HashMap target path decomposition for assignment
- Statement: `target_path_type_HashMapT_assign_target_decomp` as above.
- Approach: use existing HashMap path lemmas to obtain nonemptiness, split result, key-prefix value-subscript property, and list equalities for `REVERSE sbs`.
- Dependencies: none
- Risk: 2
- Checkpoint: no
- Not to try: do not unfold this inside the main theorem.

### C3.1.6.3: Final HashMap leaf has the runtime type needed by assign_subscripts
- Statement: `target_path_type_HashMapT_split_leaf_runtime` as above.
- Approach: convert `target_path_type` to `place_leaf_typed`, apply `place_leaf_path_typed_split_leaf_type`, then use assignability and evaluate-type well-formedness lemmas.
- Dependencies: C3.1.6.2
- Risk: 2
- Checkpoint: no
- Not to try: do not induct directly on subscript lists.

### C3.1.6.4: No TypeError through the unfolded HashMapRef assign_target branch
- Statement: optional integration helper `assign_target_HashMapRef_branch_no_type_error` with the pre-derived operational facts.
- Approach: unfold `assign_target_def` once; case split explicitly on `read_storage_slot`, `assign_subscripts`, and `write_storage_slot`; use `read_storage_slot_error`, `read_storage_slot_well_typed_value`, `assign_subscripts_no_type_error_runtime_typed`, `assign_subscripts_preserves_type_runtime_typed`, `write_storage_slot_no_type_error_from_value_has_type`, and `assign_result_no_type_error_from_successful_assign`.
- Dependencies: C3.1.6.1, C3.1.6.2, C3.1.6.3
- Risk: 2
- Checkpoint: no
- Not to try: avoid broad `TRY`-driven simplification over `AllCaseEqs()`.

## Dependency Graph

C3.1.6.1 and C3.1.6.2 are independent. C3.1.6.3 depends on the path decomposition interface from C3.1.6.2. C3.1.6.4 consumes C3.1.6.1–C3.1.6.3. The top-level theorem C3.1.6 depends on all four and can inline C3.1.6.4 if the proof remains clean.

## Notes

Stay inside the C3.1.6 subtree. Do not repair sibling branches (`ArrayRef`, `ImmutableVar`, tuple, or `assign_targets_cons`) as part of this work.

Because this is an augment-mode subtree, `required_for_completion` is false in the structured metadata even though C3.1.6 is the task-scoped obligation for this request.

If `compute_hashmap_slot ... <> NONE` is not convenient for rewriting the do-block, immediately convert it to `?final_slot. compute_hashmap_slot ... = SOME final_slot` using `optionTheory.IS_SOME_EXISTS`; then use the named `final_slot` throughout the monadic branch proof.

If the proof appears to need `assign_operation_matches_target_shape` or `assign_target_assignable`, that is a sign that too much of `assign_target` was unfolded or the wrong branch is being considered. For this BaseTargetV HashMapRef theorem, those assumptions are interface baggage and should not drive the proof.

## Structured Components

### C3: C3
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.6.2 risk 2. The source already has `target_path_type_HashMapT_assign_target_decomp`. Its proof is standard list/path reasoning plus existing HashMap path lemmas, but it is the main shape fact needed before monadic unfolding.
- Required for completion: yes

### C3.1: C3.1
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.6.2 risk 2. The source already has `target_path_type_HashMapT_assign_target_decomp`. Its proof is standard list/path reasoning plus existing HashMap path lemmas, but it is the main shape fact needed before monadic unfolding.

### C3.1.6: Top-level HashMapRef assignment cannot produce TypeError
- Kind: `proof`
- Risk: 2
- Rationale: The source already has the right boundary facts for declaration lookup, HashMap path decomposition, storage read/write, and assign_subscripts. The remaining work is integration over one assign_target branch with controlled monadic unfolding; no new semantic invariant is needed.
- Dependencies: C3.1.6.1, C3.1.6.2, C3.1.6.3, C3.1.6.4

#### Description
Prove the exact theorem `top_level_HashMapRef_assign_no_type_error` for the HashMapRef branch of `sound_TopLevelVar`. This component owns only the theorem and its strict local helper outputs.

#### Statement
```hol
runtime_consistent env cx st ==>
FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (HashMapT kt vt) ==>
target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
assignable_type (get_tenv cx) ty ==>
assign_operation_runtime_typed env ty op ==>
assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op ==>
assign_target_assignable (BaseTargetV (TopLevelVar src_id_opt id) sbs) st ==>
well_formed_vtype (get_tenv cx) (HashMapT kt vt) ==>
get_module_code cx src_id_opt = SOME code ==>
find_var_decl_by_num (string_to_num id) code = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
no_type_error_result res
```

#### Approach
First derive the deterministic setup facts: `env.type_defs = get_tenv cx`; `lookup_global cx src_id_opt (string_to_num id) st = (INL (HashMapRef is_transient (n2w slot) kt vt),st)` using C3.1.6.1; HashMap subscript decomposition using C3.1.6.2; `compute_hashmap_slot ... <> NONE`; and final leaf runtime facts using C3.1.6.3. Then hand those facts to C3.1.6.4, the monadic-branch lemma, or inline the same argument: unfold `assign_target_def` once for `TopLevelVar`, simplify known lookup/module/split/compute/evaluate cases, and eliminate the only TypeError-returning subcalls by existing storage and assignment lemmas.

#### Not to try
Do not unfold all of `target_path_type`, `place_leaf_path_typed`, or `split_hashmap_subscripts` in the main theorem. Do not do an unstructured `gvs[assign_target_def, AllCaseEqs()]` before deriving the split and final leaf facts; it creates many unrelated TypeError branches with lost equalities. The hypotheses `assign_operation_matches_target_shape` and `assign_target_assignable` are irrelevant for this BaseTargetV HashMapRef proof except to match callers; do not spend effort trying to use them.

### C3.1.6.1: HashMap declaration lookup gives a HashMapRef global value
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: This is a direct unfolding of `lookup_global_def`; current source already contains `lookup_global_HashMapVarDecl_returns_HashMapRef`.

#### Description
Provide or reuse the boundary lemma converting the static declaration/layout assumptions into the exact `lookup_global` result used by `assign_target_def`.

#### Statement
```hol
Theorem lookup_global_HashMapVarDecl_returns_HashMapRef:
  get_module_code cx src = SOME code ==>
  find_var_decl_by_num n code = SOME (HashMapVarDecl is_t kt vt, id) ==>
  lookup_var_slot_from_layout cx is_t src id = SOME slot ==>
  lookup_global cx src n st = (INL (HashMapRef is_t (n2w slot) kt vt), st)
```

#### Approach
If not already proved, unfold `lookup_global_def` with `bind_def`, `lift_option_type_def`, `return_def`, `raise_def`, option/product/type-value case rators, and the declaration/layout hypotheses. This lemma should be consumed instead of unfolding `lookup_global` in C3.1.6.

#### Not to try
Do not derive this from runtime consistency or top-level typing; it is purely operational and follows from code/layout lookup.

### C3.1.6.2: HashMap target path decomposition for assignment
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: The source already has `target_path_type_HashMapT_assign_target_decomp`. Its proof is standard list/path reasoning plus existing HashMap path lemmas, but it is the main shape fact needed before monadic unfolding.

#### Description
Provide or reuse the decomposition fact that a typed HashMap assignment path is nonempty, splits into the first HashMap key subscript, nested HashMap key subscripts, and remaining ordinary subscripts, and has enough value-shaped subscripts to compute the storage slot.

#### Statement
```hol
Theorem target_path_type_HashMapT_assign_target_decomp:
  !env kt vt sbs ty.
    well_formed_vtype env.type_defs (HashMapT kt vt) ==>
    target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
    ?first_sub rest_subs final_type kts remaining.
      REVERSE sbs = first_sub :: rest_subs /\
      first_sub = LAST sbs /\
      rest_subs = TL (REVERSE sbs) /\
      split_hashmap_subscripts vt rest_subs = SOME (final_type, kts, remaining) /\
      LENGTH kts + LENGTH remaining = LENGTH rest_subs /\
      EVERY ((<>) NONE o subscript_to_value)
        (first_sub :: TAKE (LENGTH kts) rest_subs)
```

#### Approach
Use existing facts `target_path_type_HashMapT_not_nil`, `target_path_type_HashMapT_split_hashmap_subscripts`, `split_hashmap_subscripts_some_imp`, and `target_path_type_HashMapT_hashmap_prefix_ValueSubscript`. Convert nonempty `sbs` to `REVERSE sbs = LAST sbs :: TL (REVERSE sbs)` using `SNOC_LAST_FRONT_eq`, `REVERSE_SNOC_eq`, and `TL_REVERSE_eq_REVERSE_FRONT`.

#### Not to try
Do not make the main theorem reason directly about `LAST`, `FRONT`, and `TL (REVERSE sbs)` after expanding `assign_target`; establish this decomposition first.

### C3.1.6.3: Final HashMap leaf has the runtime type needed by assign_subscripts
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: The source already has `target_path_type_HashMapT_split_leaf_runtime`. It bridges static path typing to the exact `assign_subscripts_no_type_error_runtime_typed` side conditions.
- Dependencies: C3.1.6.2

#### Description
Provide or reuse the leaf-runtime lemma extracting the final evaluated storage type, the evaluated assignment leaf type, non-`NoneTV`, and well-formedness.

#### Statement
```hol
Theorem target_path_type_HashMapT_split_leaf_runtime:
  !env cx st kt vt sbs ty rest_subs final_type kts remaining.
    runtime_consistent env cx st ==>
    well_formed_vtype (get_tenv cx) (HashMapT kt vt) ==>
    target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
    rest_subs = TL (REVERSE sbs) ==>
    split_hashmap_subscripts vt rest_subs = SOME (final_type, kts, remaining) ==>
    assignable_type (get_tenv cx) ty ==>
    ?final_tv.
      evaluate_type (get_tenv cx) final_type = SOME final_tv /\
      evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) /\
      leaf_type final_tv remaining <> NoneTV /\
      well_formed_type_value final_tv
```

#### Approach
From `runtime_consistent`, rewrite `env.type_defs = get_tenv cx`. Use `target_path_type_Type_place_leaf_typed` and `place_leaf_typed_def`; split `REVERSE sbs`, using C3.1.6.2/nonemptiness to rule out `[]`. Apply `place_leaf_path_typed_split_leaf_type`. Finally prove non-`NoneTV` from `assignable_type_evaluate_not_NoneTV` and well-formedness from `evaluate_type_well_formed_type_value`.

#### Not to try
Do not prove this by induction on `sbs`; the existing path-typing/place-leaf interface is the correct abstraction and avoids duplicating HashMap path recursion.

### C3.1.6.4: No TypeError through the unfolded HashMapRef assign_target branch
- Kind: `integration_lemma`
- Risk: 2
- Rationale: This is a linear do-block proof once all successful option computations are known and each potentially TypeError-producing subcall has a boundary lemma. The source currently attempts this inline; extracting it is the robust way to avoid brittle `TRY` scripts.
- Dependencies: C3.1.6.1, C3.1.6.2, C3.1.6.3

#### Description
Optional but recommended helper: isolate the monadic branch proof after all path and slot facts have been derived. If the executor can make the main theorem concise without this helper, it may inline the proof, but it must preserve this proof boundary conceptually.

#### Statement
Suggested helper shape:
```hol
Theorem assign_target_HashMapRef_branch_no_type_error:
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (HashMapRef is_transient (n2w slot) kt vt), st) ==>
  get_module_code cx src_id_opt = SOME code ==>
  REVERSE sbs = first_sub :: rest_subs ==>
  split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,remaining) ==>
  compute_hashmap_slot (n2w slot) (kt::kts)
    (first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining) rest_subs) <> NONE ==>
  evaluate_type (get_tenv cx) final_type = SOME final_tv ==>
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) ==>
  leaf_type final_tv remaining <> NoneTV ==>
  well_formed_type_value final_tv ==>
  assign_operation_runtime_typed env ty op ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```
If `compute_hashmap_slot <> NONE` is awkward to consume under `lift_option_type`, strengthen the helper by existentially naming `final_slot` with `compute_hashmap_slot ... = SOME final_slot`; derive it in C3.1.6 from `<> NONE` using `optionTheory.IS_SOME_EXISTS`.

#### Approach
Unfold `assign_target_def` once and reduce the known `lookup_global`, `get_module_code`, nonempty reverse, `split_hashmap_subscripts`, `compute_hashmap_slot`, and `evaluate_type` cases. Then case split on `read_storage_slot ... final_tv st`:
1. If it returns `INR (Error (TypeError msg))`, contradict with `read_storage_slot_error` (or the imported equivalent).
2. If it returns another error, `no_type_error_result` holds for that result.
3. If it returns `INL current_val`, derive `value_has_type final_tv current_val` via `read_storage_slot_well_typed_value` and `well_formed_type_value final_tv`.
For `assign_subscripts final_tv current_val remaining op`, a TypeError result is impossible by `assign_subscripts_no_type_error_runtime_typed` using the evaluated leaf type and `assign_operation_runtime_typed`. If `assign_subscripts` succeeds with `new_val`, derive `value_has_type final_tv new_val` by `assign_subscripts_preserves_type_runtime_typed`, rule out TypeError in `write_storage_slot` via `write_storage_slot_no_type_error_from_value_has_type`, and rule out TypeError in `assign_result` via `assign_result_no_type_error_from_successful_assign`.

#### Not to try
Do not rely on repeated `TRY` blocks after a broad `simp[AllCaseEqs()]`; that was the previous brittle failure mode. Name the results of `read_storage_slot`, `assign_subscripts`, and `write_storage_slot` with `Cases_on`, and apply the relevant no-TypeError lemma in each branch.

---

## PLAN AUGMENT: C3.1.7 @ 2026-05-14T05:30:45+00:00

# PLAN: C3.1.7 — integrate `top_level_HashMapRef_assign_no_type_error` into `sound_TopLevelVar`

## Argument

This augment owns only the HashMapRef sub-branch of `Resume assign_target_sound_mutual[sound_TopLevelVar]`. The mathematical work for HashMapRef no-TypeError has already been isolated in the boundary theorem:

```sml
top_level_HashMapRef_assign_no_type_error
```

So integration should not re-open the HashMap assignment do-block. In the mutual theorem's `TopLevelVar` case, after unfolding enough of `assign_target_def` and `assign_target_assignable_context_def`, the semantic branch has a successful top-level lookup returning a `HashMapRef is_transient ... t v`. The target typing hypothesis supplies `target_runtime_typed env cx st tgt ty (BaseTargetV (TopLevelVar src_id_opt id) sbs)`. In the top-level-location case, this decomposes into:

1. static top-level type lookup for the variable,
2. `location_runtime_typed env cx st (TopLevelVar src_id_opt id) vt`, and
3. `target_path_type env vt sbs (Type ty)`.

The semantic `HashMapRef` branch and declaration-consistency lemmas force `vt = HashMapT t v`. The strengthened context hypothesis supplies the concrete declaration and layout witnesses needed by the standalone theorem: module code, `HashMapVarDecl`, and slot lookup. The mutual theorem also already has `runtime_consistent`, `assignable_type env.type_defs ty`, `assign_operation_runtime_typed env ty op`, `assign_operation_matches_target_shape ... op`, and the context hypothesis; `runtime_consistent` gives `env.type_defs = get_tenv cx`, converting assignability to the standalone theorem's form.

Therefore the branch is just premise extraction plus one invocation of `top_level_HashMapRef_assign_no_type_error`. State preservation for this component is already handled by the first conjunct call to `assign_target_preserves_state_well_typed_mutual`; C3.1.7 must only discharge the no-TypeError conjunct for this HashMapRef semantic branch.

## Definition Design

No new definitions are needed.

- `assign_target_assignable_context_def`
  - Purpose: carries the concrete top-level assignability facts the standalone theorem needs: nonempty path, module code, declaration shape, and layout slot.
  - Shape: case split on target value. In the `TopLevelVar`/HashMapRef branch it exposes existential witnesses; use `gvs[IS_SOME_EXISTS]` only locally after the semantic branch is selected.
  - Boundary: consumers should use the exposed witnesses directly; do not unfold declaration/layout lookup definitions.
  - Probe: after simplification, there should be hypotheses for `get_module_code`, `find_var_decl_by_num ... = SOME (HashMapVarDecl ... , ...)`, and `lookup_var_slot_from_layout ... = SOME ...`.
  - Failure sign: if these witnesses are absent, the proof unfolded the wrong branch or lost the selected `HashMapRef` equality.

- `target_runtime_typed_def` and `location_runtime_typed_def`
  - Purpose: connect the concrete runtime target to its static Vyper type and path typing.
  - Shape: for `BaseTargetV (TopLevelVar ... ) sbs`, simplification should expose top-level lookup and `target_path_type env vt sbs (Type ty)`.
  - Boundary: use `top_level_HashMap_decl`, `top_level_Type_not_hashmap_decl`, and `location_runtime_typed_well_formed_vtype` to identify/validate `HashMapT t v`; avoid unfolding environment consistency internals except for `env.type_defs = get_tenv cx`.
  - Probe: prove `vt = HashMapT t v` in the selected branch before invoking the standalone theorem.
  - Failure sign: broad simplification destructs `vt` too early and loses the declaration facts.

- `top_level_HashMapRef_assign_no_type_error`
  - Purpose: sole no-TypeError boundary for this semantic branch.
  - Shape: theorem premise list exactly matches the facts available from the mutual branch plus the context witnesses.
  - Boundary: do not unfold `assign_target_def` inside C3.1.7 after reaching this theorem; if invocation is hard, package missing premises in a tiny local extraction lemma instead.
  - Probe: a `drule`/`qspecl` invocation with `t` and `v` should leave only premise-matching subgoals, not monadic assignment subgoals.
  - Failure sign: any subgoal mentioning `compute_hashmap_slot`, `split_hashmap_subscripts`, `read_storage_slot`, or `assign_subscripts` means the branch theorem was not used at the correct abstraction level.

## Code Structure

Work only in `semantics/prop/vyperTypeStatePreservationScript.sml`, inside the existing `Resume assign_target_sound_mutual[sound_TopLevelVar]` proof. Do not edit the sibling `ArrayRef` branch cheat or later `ImmutableVar`/`TupleTargetV`/`assign_targets_cons` resumes under this augment. If the current inlined proof is brittle, the only permitted helper owned by this subtree is a local premise-extraction lemma immediately before the resume, named for the HashMapRef integration branch; it must not mention ArrayRef or other target forms.

## Components

### C3.1.7: Integrate HashMapRef boundary theorem into `sound_TopLevelVar`
- Statement: close exactly the HashMapRef sub-branch in `Resume assign_target_sound_mutual[sound_TopLevelVar]` by invoking `top_level_HashMapRef_assign_no_type_error`; leave sibling branches unchanged.
- Approach: select the `HashMapRef` semantic branch after the existing top-level simplification, extract declaration/layout witnesses from `assign_target_assignable_context_def`, prove the selected static type is `HashMapT t v`, convert `assignable_type env.type_defs ty` to `assignable_type (get_tenv cx) ty`, and invoke the standalone theorem with the original `assign_target ... = (res,st')` equation.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3
- Risk: 2
- Checkpoint: yes
- Not to try: do not unfold the HashMapRef branch of `assign_target_def` after this point; do not attempt to prove preservation here; do not touch the following ArrayRef `cheat`.

### C3.1.7.1: Extract top-level HashMapRef context witnesses
- Statement: in the selected `TopLevelVar`/`HashMapRef` branch, obtain the `get_module_code`, `find_var_decl_by_num ... = SOME (HashMapVarDecl is_transient t v, id_str)`, and `lookup_var_slot_from_layout ... = SOME slot` facts required by `top_level_HashMapRef_assign_no_type_error`.
- Approach: unfold/simplify only `assign_target_assignable_context_def` and use `IS_SOME_EXISTS` to name the declaration and slot witnesses. Keep the semantic branch equality and target location facts in context while simplifying.
- Dependencies: none
- Risk: 1
- Checkpoint: no
- Not to try: do not unfold `lookup_global_def`; declaration/layout facts should come from assignability context, not from re-executing lookup.

### C3.1.7.2: Identify the static top-level type as `HashMapT t v`
- Statement: in the selected branch, prove the static type `vt`/top-level vtype used by `target_runtime_typed` is equal to `HashMapT t v`, and derive `well_formed_vtype (get_tenv cx) (HashMapT t v)`.
- Approach: after `Cases_on tgt` and simplification of `target_runtime_typed_def`/`location_runtime_typed_def`, rule out non-hashmap declarations using `top_level_Type_not_hashmap_decl`; use `top_level_HashMap_decl` for the hashmap declaration case. For well-formedness, either rewrite with `env.type_defs = get_tenv cx` from `runtime_consistent`, or use `location_runtime_typed_well_formed_vtype` on `location_runtime_typed env cx st (TopLevelVar src_id_opt id) (HashMapT t v)`.
- Dependencies: C3.1.7.1
- Risk: 2
- Checkpoint: no
- Not to try: do not case-split repeatedly on the concrete `HashMapRef` runtime value; the important case split is on the static vtype/declaration correspondence.

### C3.1.7.3: Invoke `top_level_HashMapRef_assign_no_type_error`
- Statement: apply the standalone theorem to conclude `no_type_error_result res` for the current HashMapRef sub-branch.
- Approach: derive `env.type_defs = get_tenv cx` from `runtime_consistent_def`, `env_consistent_def`, and `env_context_consistent_def`. Rewrite the mutual theorem's `assignable_type env.type_defs ty` to the theorem's `assignable_type (get_tenv cx) ty`. Supply `FLOOKUP env.toplevel_vtypes ... = SOME (HashMapT t v)` and `target_path_type env (HashMapT t v) sbs (Type ty)` from C3.1.7.2/target-runtime decomposition; supply operation-shape, assignability context, declaration/layout witnesses, and the original `assign_target ... = (res,st')` equation directly.
- Dependencies: C3.1.7.2
- Risk: 1
- Checkpoint: no
- Not to try: do not simplify with `AllCaseEqs()` after invoking the theorem; that can reopen the monadic branch and obscure the theorem application.

### C3.1.7.4: Optional local packaging lemma if direct premise matching is brittle
- Statement: only if C3.1.7.3 becomes syntactically unstable, add a local helper immediately before the resume that packages C3.1.7.1–C3.1.7.3 into a theorem whose conclusion is `no_type_error_result res` for the selected TopLevelVar/HashMapRef branch.
- Approach: the helper must have hypotheses no broader than the selected branch facts already present in the resume plus the original mutual theorem premises, and its proof must end by invoking `top_level_HashMapRef_assign_no_type_error`. This is a strict helper output owned by C3.1.7, not a reusable assignment theorem.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3
- Risk: 2
- Checkpoint: no
- Not to try: do not generalize this helper to all top-level references or arrays; that would escape the C3.1.7 subtree.

## Dependency Graph

C3.1.7.1 → C3.1.7.2 → C3.1.7.3 → C3.1.7. C3.1.7.4 is optional and depends on the same extraction/type-identification work; use it only if direct invocation in the resume is too brittle.

## Notes

- This augment intentionally leaves the `ArrayRef` branch cheat following the HashMapRef branch untouched. If holbuild still reports a cheat at the end of `sound_TopLevelVar`, verify whether it is the sibling ArrayRef branch before expanding this subtree.
- If the current proof text already contains a near-complete HashMapRef branch, the executor should stabilize it rather than rewrite the entire resume.
- If `top_level_HashMapRef_assign_no_type_error` itself fails to build, that is outside C3.1.7 and requires a broader C3.1 replan, not edits in this integration subtree.

## Structured Components

### C3: C3
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.2 risk 2. Uses existing branch-consistency lemmas (`top_level_Type_not_hashmap_decl`, `top_level_HashMap_decl`, `location_runtime_typed_well_formed_vtype`) but variable names after simplification may require care.
- Required for completion: yes

### C3.1: C3.1
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.2 risk 2. Uses existing branch-consistency lemmas (`top_level_Type_not_hashmap_decl`, `top_level_HashMap_decl`, `location_runtime_typed_well_formed_vtype`) but variable names after simplification may require care.

### C3.1.7: Integrate HashMapRef boundary theorem into sound_TopLevelVar
- Kind: `proof`
- Risk: 2
- Rationale: The hard HashMapRef monadic proof is already isolated in `top_level_HashMapRef_assign_no_type_error`; this component is premise extraction and theorem invocation inside one selected branch. Remaining risk is syntactic brittleness from the existing broad simplification.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3
- Checkpoint: yes

#### Description
Close exactly the HashMapRef sub-branch in `Resume assign_target_sound_mutual[sound_TopLevelVar]`; do not touch ArrayRef or later sibling resumes.

#### Statement
Selected branch obligation inside the mutual proof: conclude `no_type_error_result res` for `assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res,st')` when lookup has selected the `HashMapRef` runtime branch.

#### Approach
After selecting the semantic HashMapRef branch, extract declaration/layout witnesses from `assign_target_assignable_context_def`, identify the static type as `HashMapT t v`, rewrite `env.type_defs = get_tenv cx`, then invoke `top_level_HashMapRef_assign_no_type_error`.

#### Not to try
Do not unfold the HashMapRef do-block again; do not prove state preservation here; do not edit the following ArrayRef cheat.

### C3.1.7.1: Extract top-level HashMapRef context witnesses
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: This is direct simplification of the strengthened `assign_target_assignable_context_def` in the already-selected top-level branch, plus `IS_SOME_EXISTS` for witnesses.

#### Description
Expose the concrete module/declaration/layout hypotheses needed by the standalone theorem.

#### Statement
Within the selected branch, obtain facts of the form `get_module_code cx src_id_opt = SOME code`, `find_var_decl_by_num (string_to_num id) code = SOME (HashMapVarDecl is_transient t v,id_str)`, and `lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot`.

#### Approach
Simplify `assign_target_assignable_context_def` locally and name existential witnesses with `IS_SOME_EXISTS`. Preserve the semantic branch equality and target typing facts.

#### Not to try
Do not unfold `lookup_global_def`; these facts come from context assignability.

### C3.1.7.2: Identify static type as HashMapT and derive well-formedness
- Kind: `proof_step`
- Risk: 2
- Rationale: Uses existing branch-consistency lemmas (`top_level_Type_not_hashmap_decl`, `top_level_HashMap_decl`, `location_runtime_typed_well_formed_vtype`) but variable names after simplification may require care.
- Dependencies: C3.1.7.1

#### Description
Connect the runtime `HashMapRef ... t v` branch to the static target type required by `top_level_HashMapRef_assign_no_type_error`.

#### Statement
Prove the target vtype in the selected TopLevelVar case is `HashMapT t v`, and obtain `well_formed_vtype (get_tenv cx) (HashMapT t v)`.

#### Approach
Use target-runtime/location-runtime decomposition, rule out non-hashmap declarations with `top_level_Type_not_hashmap_decl`, use `top_level_HashMap_decl` for the hashmap case, and derive well-formedness via `location_runtime_typed_well_formed_vtype` or by rewriting `env.type_defs = get_tenv cx`.

#### Not to try
Do not repeatedly destruct the runtime `HashMapRef`; focus on the static vtype/declaration link.

### C3.1.7.3: Invoke top_level_HashMapRef_assign_no_type_error
- Kind: `proof_step`
- Risk: 1
- Rationale: Once C3.1.7.1 and C3.1.7.2 are in context, this is a direct theorem application with a simple environment-type rewrite.
- Dependencies: C3.1.7.2

#### Description
Finish the selected branch by applying the standalone HashMapRef no-TypeError theorem.

#### Statement
Conclude `no_type_error_result res` from the branch facts and original `assign_target ... = (res,st')` equation.

#### Approach
Derive `env.type_defs = get_tenv cx` from runtime consistency, rewrite assignability, and supply all theorem premises from the mutual hypotheses and extraction/type-identification facts.

#### Not to try
Do not simplify with broad `AllCaseEqs()` after the theorem application; it can reopen the monadic computation.

### C3.1.7.4: Optional local packaging lemma for brittle premise matching
- Kind: `optional_helper`
- Risk: 2
- Rationale: If the inline resume proof is unstable, a tiny local wrapper is a standard way to freeze premise extraction while staying inside the C3.1.7 subtree.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3

#### Description
Use only if direct invocation of the standalone theorem in the resume remains syntactically brittle.

#### Statement
A local helper whose hypotheses are exactly the selected HashMapRef branch facts plus original mutual premises, with conclusion `no_type_error_result res`.

#### Approach
Prove by the same extraction/type-identification steps and end with `top_level_HashMapRef_assign_no_type_error`; place immediately before the resume.

#### Not to try
Do not generalize to ArrayRef or all top-level assignment forms.

---

## PLAN AUGMENT: C3.1.7.1 @ 2026-05-14T09:22:47+00:00

# PLAN: C3.1.7.1 — close non-array StorageVarDecl/Value cases in `sound_TopLevelVar`

## Argument

Within this augment scope, the only obligation is the `vt = Type t` / `StorageVarDecl` part of `Resume assign_target_sound_mutual[sound_TopLevelVar]` in `vyperTypeStatePreservationScript.sml`, specifically the five non-array `root_tv` constructor leaves currently discharged by cheats: `BaseTV`, `TupleTV`, `StructTV`, `FlagTV`, and `NoneTV`.

Mathematically these five branches are not separate semantic cases. Once the branch has established that the top-level variable is a `StorageVarDecl`, has a layout slot, and its declared type evaluates to `root_tv`, every non-`ArrayTV` root type follows from the same boundary theorem:

```sml
assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error
```

That theorem packages the lookup-global analysis: `HashMapRef` contradicts `StorageVarDecl`, `ArrayRef` contradicts the non-array root type, and the remaining `Value` branch is handled by the existing value-assignment no-TypeError boundary. Therefore each of the five cheated leaves only needs to provide the side condition

```sml
!elem_tv bd. root_tv <> ArrayTV elem_tv bd
```

which is immediate by datatype constructor discrimination.

The previous escalation is a tooling/proof-runtime issue, not a mathematical one: resolution tactics (`drule`, `irule`, `metis_tac`, `goal_assum`, by-subgoal scripts) trigger a `DISCH_THEN` instrumentation assertion in this file. This subtree must therefore integrate the already proved theorem using a simplifier-shaped adapter or another resolution-free exact application style. Do not reopen storage semantics.

## Definition Design

No definitions should be changed in this subtree.

- `assign_target_sound_mutual` already has the correct strengthened side-condition interface.
- `target_runtime_typed`, `location_runtime_typed`, and `assign_target_assignable_context` already expose the facts needed by the boundary theorem before the root-tv split.
- `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` is the correct consumer boundary for this component. Consumers should use it rather than unfolding `assign_target_def`, `lookup_global_def`, `read_storage_slot`, or `write_storage_slot`.

### Probe

The empirical design check is C3.1.7.1.1: confirm the boundary theorem is present before the resume and that the branch facts align with its hypotheses.

### Failure signs

If the branch lacks one of the boundary theorem's hypotheses after the existing witness extraction, that is a local branch-fact alignment problem and should be escalated with the residual goal. If applying the theorem fails only with the known `DISCH_THEN` instrumentation assertion, use the C3.1.7.1.2 adapter path; do not redesign definitions or weaken the theorem.

## Code Structure

All work stays in `semantics/prop/vyperTypeStatePreservationScript.sml`.

- Prefer no new theorem if direct simplifier/exact application of `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` closes the five leaves.
- If the proof-runtime issue blocks direct use, add only the strict local adapter `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error_conj` immediately after the existing boundary theorem and before `Resume assign_target_sound_mutual[sound_TopLevelVar]`.
- Do not move helpers to libraries; this is a local top-level assignment branch adapter.
- Do not edit sibling branches (`HashMapRef`, `ArrayRef`, `ImmutableVar`, tuple/list targets) in this augment.

## Components

### C3.1.7.1: Close the non-array StorageVarDecl/Value cases
- Kind: proof_subtree
- Risk: 2
- Dependencies: C3.1.7.1.1
- Checkpoint: yes
- Required for completion: false (inherited from the parent task component; this augment cannot mark dotted IDs as top-level-required)

Replace exactly the five non-array constructor cheats in `Resume assign_target_sound_mutual[sound_TopLevelVar]`. The proof is by the existing `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` boundary theorem plus constructor discrimination.

Not to try: do not unfold assignment/storage internals, do not reopen HashMapRef, and do not use resolution tactics known to trigger the proof-runtime assertion.

### C3.1.7.1.1: Boundary-theorem availability and branch-fact alignment
- Kind: probe
- Risk: 1
- Dependencies: none
- Checkpoint: no

Confirm that `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` is available and that the current branch supplies its hypotheses. This is a mechanical source alignment check, not a new proof architecture.

### C3.1.7.1.2: Add a resolution-free conjunctive adapter if needed
- Kind: strict_helper
- Risk: 2
- Dependencies: C3.1.7.1.1
- Checkpoint: no

If direct use of the existing theorem triggers the known `DISCH_THEN` proof-runtime assertion, add a local conjunctive adapter:

```sml
Theorem assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error_conj:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) /\
  target_path_type env (Type t) sbs (Type ty) /\
  assignable_type (get_tenv cx) ty /\
  assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op /\
  env.type_defs = get_tenv cx /\
  get_module_code cx src_id_opt = SOME code /\
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) /\
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME root_tv /\
  well_formed_type_value root_tv /\
  (!elem_tv bd. root_tv <> ArrayTV elem_tv bd) /\
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```

Prove it only from the existing curried theorem, preferably with pure simplification. If even this adapter cannot be proved without the instrumentation failure, escalate with the exact build output.

### C3.1.7.1.3: Replace the five constructor cheats
- Kind: proof
- Risk: 2
- Dependencies: C3.1.7.1.1, and C3.1.7.1.2 if added
- Checkpoint: yes

For `BaseTV`, `TupleTV`, `StructTV`, `FlagTV`, and `NoneTV`, simplify the constructor-discrimination side condition and close with the boundary theorem or the conjunctive adapter. Leave the existing `ArrayTV` branch as-is.

## Dependency Graph

C3.1.7.1.1 → C3.1.7.1.3 → C3.1.7.1

C3.1.7.1.2 is an optional strict helper between C3.1.7.1.1 and C3.1.7.1.3 if direct theorem use is blocked by the known proof-runtime issue.

## Notes

- The current source already contains a proved `top_level_HashMapRef_assign_no_type_error`; this augment does not touch it.
- The `ArrayTV` branch is outside this component and should remain delegated to `assign_target_TopLevelVar_ArrayRef_branch_no_type_error` as in the current source.
- If completing these five leaves reveals a missing hypothesis not covered by the existing boundary theorem, report the exact residual goal. That would indicate branch-fact drift, not permission to weaken `assign_target_sound_mutual`.
- If all resolution-free theorem-application styles are blocked by the same proof-runtime instrumentation failure, escalate as a tooling blocker. Do not respond by duplicating the semantic proof inline.

## Structured Components

### C3: C3
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.1.2 risk 2. The earlier stuck episode was caused by proof-runtime instrumentation around resolution tactics. A conjunctive/simplifier-shaped corollary is a local adapter around an already proved boundary theorem and avoids redoing semantic case analysis.
- Required for completion: yes

### C3.1: C3.1
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.1.2 risk 2. The earlier stuck episode was caused by proof-runtime instrumentation around resolution tactics. A conjunctive/simplifier-shaped corollary is a local adapter around an already proved boundary theorem and avoids redoing semantic case analysis.

### C3.1.7: C3.1.7
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.1.2 risk 2. The earlier stuck episode was caused by proof-runtime instrumentation around resolution tactics. A conjunctive/simplifier-shaped corollary is a local adapter around an already proved boundary theorem and avoids redoing semantic case analysis.

### C3.1.7.1: Close the non-array StorageVarDecl/Value cases in sound_TopLevelVar
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The mathematical obligation is already isolated: for `vt = Type t` and `vdi = StorageVarDecl`, all non-`ArrayTV` root constructors reduce to the existing boundary theorem `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`. The prior blocker is proof-runtime instrumentation around resolution tactics, so this subtree uses only existing boundary facts and resolution-free/simplifier-oriented integration.
- Dependencies: C3.1.7.1.1
- Checkpoint: yes

#### Description
Replace exactly the five remaining non-array constructor cheats in the `vt = Type t` branch of `Resume assign_target_sound_mutual[sound_TopLevelVar]` in `vyperTypeStatePreservationScript.sml`: `BaseTV`, `TupleTV`, `StructTV`, `FlagTV`, and `NoneTV`. Leave the `ArrayTV` branch and all sibling suspended branches outside this component untouched unless they are strict consequences of this edit.

#### Statement
For each non-array `root_tv` constructor in the current `StorageVarDecl` branch, prove the no-TypeError conjunct of `assign_target_sound_mutual[sound_TopLevelVar]`:

```sml
no_type_error_result res
```

under the already established local facts used by
`assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`.

#### Approach
Use the existing boundary theorem:

```sml
assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error
```

It packages the lookup-global `Value` branch and excludes `HashMapRef`/`ArrayRef` for a non-array storage declaration. After the existing code has produced witnesses for `code`, `vdi = StorageVarDecl is_transient typ`, `id_str`, `slot`, `root_tv`, `evaluate_type ... typ = SOME root_tv`, and `well_formed_type_value root_tv`, each non-array constructor only needs the side condition `!elem_tv bd. root_tv <> ArrayTV elem_tv bd`, which is immediate by constructor discrimination. Prefer a single helper/tactic pattern or simplifier corollary shared by all five cases instead of five distinct mini-proofs.

#### Not to try
Do not reopen the already proved HashMapRef helper path. Do not unfold `assign_target_def`, `lookup_global_def`, or storage read/write internals in these five cases. Do not use `drule`, `irule`, `metis_tac`, `goal_assum`, or by-subgoal proof scripts in this subtree unless a preliminary build shows the proof-runtime instrumentation issue has disappeared.

### C3.1.7.1.1: Boundary-theorem availability and branch-fact alignment
- Kind: `probe`
- Risk: 1
- Rationale: This is a mechanical check against current source: the boundary theorem is present immediately before the resume, and the existing branch code already derives its hypotheses before the root-tv case split.

#### Description
Before editing the five cheats, verify that the branch facts match the boundary theorem exactly enough for simplifier/kernal application. This component produces no new architecture and should not add broad lemmas.

#### Statement
Confirm the following theorem is available in `vyperTypeStatePreservationScript.sml` before `Resume assign_target_sound_mutual[sound_TopLevelVar]`:

```sml
Theorem assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) ==>
  target_path_type env (Type t) sbs (Type ty) ==>
  assignable_type (get_tenv cx) ty ==>
  assign_operation_runtime_typed env ty op ==>
  assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op ==>
  env.type_defs = get_tenv cx ==>
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  well_formed_type_value root_tv ==>
  (!elem_tv bd. root_tv <> ArrayTV elem_tv bd) ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```

#### Approach
Inspect the local assumptions after the current `Cases_on root_tv` split. The `vt = Type t` branch should still contain the `FLOOKUP` and `target_path_type` facts from `target_runtime_typed_def/location_runtime_typed_def`, the operation typing and shape hypotheses from the mutual theorem, and the declaration/layout/evaluate-type witnesses just derived in the script. If a variable name differs, instantiate the theorem with the branch's variables rather than changing the theorem statement.

#### Not to try
Do not add a new duplicate of this theorem. If it is absent in the executor's checkout, stop and escalate because that means this subtree is not aligned with the current source snapshot.

### C3.1.7.1.2: Add a resolution-free corollary for simplifier integration if needed
- Kind: `strict_helper`
- Risk: 2
- Rationale: The earlier stuck episode was caused by proof-runtime instrumentation around resolution tactics. A conjunctive/simplifier-shaped corollary is a local adapter around an already proved boundary theorem and avoids redoing semantic case analysis.
- Dependencies: C3.1.7.1.1

#### Description
If direct use of `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` in the resume triggers the DISCH_THEN/proof-runtime assertion, add this local adapter immediately after the existing boundary theorem and before the resume. Skip this component if the final branch closes directly with the existing theorem.

#### Statement
Preferred adapter shape:

```sml
Theorem assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error_conj:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) /\
  target_path_type env (Type t) sbs (Type ty) /\
  assignable_type (get_tenv cx) ty /\
  assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op /\
  env.type_defs = get_tenv cx /\
  get_module_code cx src_id_opt = SOME code /\
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) /\
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME root_tv /\
  well_formed_type_value root_tv /\
  (!elem_tv bd. root_tv <> ArrayTV elem_tv bd) /\
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```

Prove it only as a local interface adapter from the existing curried theorem.

#### Approach
Try a pure simplifier proof first, e.g. the theorem should be reducible by `simp[assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error]` because the conclusion is exactly the old theorem with conjunctions replacing implication chaining. Do not use resolution tactics in this proof. If the simplifier still triggers the same proof-runtime assertion, do not keep experimenting with equivalent resolution scripts; escalate with the exact residual/build output.

#### Not to try
Do not prove this corollary by unfolding `assign_target_def`; that duplicates the already proved boundary theorem and re-enters the HashMapRef/ArrayRef cases. Do not use `metis_tac`/`prove_tac` as a shortcut; prior evidence says those paths are intercepted by the broken proof instrumentation.

### C3.1.7.1.3: Replace the five non-array constructor cheats
- Kind: `proof`
- Risk: 2
- Rationale: Once the branch facts are aligned and optionally a conjunctive adapter exists, each constructor case is the same non-array argument plus constructor discrimination. No semantic recursion or new invariant is involved.
- Dependencies: C3.1.7.1.1
- Checkpoint: yes

#### Description
Edit only the five cheated leaves currently written as `(* BaseTV *) cheat`, `(* TupleTV *) cheat`, `(* StructTV *) cheat`, `(* FlagTV *) cheat`, and `(* NoneTV *) cheat` in `Resume assign_target_sound_mutual[sound_TopLevelVar]`. If C3.1.7.1.2 was added, use its `_conj` corollary; otherwise use the original boundary theorem.

#### Statement
Each leaf proves:

```sml
no_type_error_result res
```

from the current assumptions plus the constructor-specific fact:

```sml
!elem_tv bd. root_tv <> ArrayTV elem_tv bd
```

#### Approach
For each constructor case, first let simplification establish the non-array side condition by datatype discrimination. Then close with the boundary theorem/adapter. The intended final proof should be structurally small: no case split below `assign_target`, no storage operation analysis, and no recomputation of `lookup_global`. If direct simplification with the boundary theorem is insufficient, use a low-level exact theorem application style that does not invoke HOL resolution tactics; this is an implementation workaround, not a mathematical redesign.

#### Not to try
Do not touch the existing `ArrayTV` branch, which already delegates to `assign_target_TopLevelVar_ArrayRef_branch_no_type_error`. Do not modify `assign_target_sound_mutual` hypotheses. Do not add broad generic lemmas about all top-level variables.

---

## PLAN AUGMENT: C3.1.7 @ 2026-05-14T10:22:10+00:00

# PLAN: C3.1.7 TopLevelVar assignment-target soundness branch

## Argument

The old C3.1.7/E0041 proof tried to prove `assign_target_sound_mutual[sound_TopLevelVar]` directly after expanding evaluator definitions, leaving resolution stuck on destructured pairs and hidden branch facts. That route is superseded. The correct argument is by a boundary decomposition matching the runtime top-level value shape:

1. The state-well-typed conjunct of the mutual branch is independent and follows from `assign_target_preserves_state_well_typed_mutual`.
2. The no-TypeError conjunct reduces through `target_runtime_typed_def`, `target_value_shape_def`, and `location_runtime_typed_def` to the static top-level vtype `vt` for `(src_id_opt,string_to_num id)`.
3. If `vt = Type t`, `assign_target_assignable_context` and context consistency identify a `StorageVarDecl`; then the evaluated root storage type either is an array, routed to the ArrayRef boundary, or is not an array, routed to the StorageVarDecl/Value boundary.
4. If `vt = HashMapT kt vt`, context consistency identifies a `HashMapVarDecl` and a layout slot; the existing HashMapRef boundary proves no TypeError.

The only active blocker is the Value subcase inside the StorageVarDecl boundary: the caller needs the exact leaf equation `evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))`. This is not a simplifier fact. It follows from the static path typing bridge to `place_leaf_typed`, plus the declaration equality `typ = t` and `env.type_defs = get_tenv cx`.

## Definition Design

No definition changes are authorized or needed in C3.1.7.

- `target_path_type` is the consumer-facing static path relation. It should not be unfolded in the parent branch except through existing bridge lemmas.
- `place_leaf_typed` / `place_leaf_path_typed` are the right boundary for recovering the concrete evaluated leaf type. The adapter lemma may unfold these definitions locally because its purpose is exactly to expose the leaf `evaluate_type` normal form.
- `assign_target_assignable_context` remains the source of declaration/layout witnesses. Consumers should extract witnesses from it, then call branch boundary theorems; they should not unfold `assign_target_def` in the mutual branch.

Probe/failure signs within this subtree:
- If `TopLevelVar_Type_StorageVarDecl_leaf_evaluate_type` is hard to prove without unfolding evaluator code, the adapter is stated with the wrong hypotheses.
- If the parent branch still needs `assign_target_def` after the boundary calls, a boundary hypothesis is missing, not a definition problem.

## Code Structure

Keep all new lemmas local to `semantics/prop/vyperTypeStatePreservationScript.sml`, near the existing TopLevelVar helper block around `assign_target_TopLevelVar_Value_branch_ntr` and `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`. Do not move definitions or create a new library for this narrow adapter.

Add two strict helper outputs owned by C3.1.7.1.3:

- `TopLevelVar_Type_StorageVarDecl_leaf_evaluate_type`
- `TopLevelVar_Type_StorageVarDecl_leaf_not_NoneTV`

Then patch `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` to use them. Avoid `DISCH_THEN` instrumentation in new proofs in this file; use explicit assertions, `rpt strip_tac`, `drule_all`, `irule`, and controlled `gvs` instead.

## Components

### C3.1.7: TopLevelVar branch of assign_target_sound_mutual
- Statement: `Resume assign_target_sound_mutual[sound_TopLevelVar]: ... QED` without cheats.
- Approach: Use the decomposed branch proof; do not revive E0041. Dispatch Type/StorageVarDecl, ArrayRef, and HashMapRef cases through their boundary lemmas.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3, C3.1.7.4
- Risk: 2
- Checkpoint: yes
- Not to try: no direct `assign_target_def`/large-`metis_tac` proof of the whole branch.

### C3.1.7.1: Type/StorageVarDecl boundary
- Statement: retain/prove `assign_target_TopLevelVar_Value_branch_ntr` and `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`.
- Approach: Keep the Value branch lemma as the evaluator-expansion boundary. Patch the StorageVarDecl wrapper by deriving the leaf evaluate-type and non-None facts explicitly via C3.1.7.1.3.
- Dependencies: C3.1.7.1.3
- Risk: 2
- Checkpoint: no
- Not to try: do not inline the Value branch proof into the wrapper.

### C3.1.7.1.3: Active leaf adapter
- Statement: provide exact leaf equation and non-None leaf side condition for Type StorageVarDecl paths.
- Approach: Chain `top_level_Type_storage_decl`, `top_level_vtype_well_formed`, `target_path_type_Type_place_leaf_typed`, `place_leaf_typed_def`, `place_leaf_path_typed_def`, and `assignable_type_evaluate_not_NoneTV`.
- Dependencies: C3.1.7.1.3.1, C3.1.7.1.3.2, C3.1.7.1.3.3
- Risk: 2
- Checkpoint: no
- Not to try: no bare `simp[]` or giant `metis_tac` for the whole chain.

### C3.1.7.1.3.1: Leaf evaluate_type equation
- Statement:
```sml
Theorem TopLevelVar_Type_StorageVarDecl_leaf_evaluate_type:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) /\
  target_path_type env (Type t) sbs (Type ty) /\
  env.type_defs = get_tenv cx /\
  get_module_code cx src_id_opt = SOME code /\
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) /\
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))
```
- Approach: Derive `typ = t`, derive well-formedness of `Type t`, obtain `place_leaf_typed`, then unfold the place-leaf definitions to expose the equation.
- Dependencies: none
- Risk: 2
- Checkpoint: no
- Not to try: do not add unnecessary `assignable_type` to this lemma.

### C3.1.7.1.3.2: Leaf non-None fact
- Statement:
```sml
Theorem TopLevelVar_Type_StorageVarDecl_leaf_not_NoneTV:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) /\
  target_path_type env (Type t) sbs (Type ty) /\
  assignable_type (get_tenv cx) ty /\
  env.type_defs = get_tenv cx /\
  get_module_code cx src_id_opt = SOME code /\
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) /\
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  leaf_type root_tv (REVERSE sbs) <> NoneTV
```
- Approach: Apply C3.1.7.1.3.1, then `assignable_type_evaluate_not_NoneTV`.
- Dependencies: C3.1.7.1.3.1
- Risk: 1
- Checkpoint: no
- Not to try: do not unfold `assignable_type`.

### C3.1.7.1.3.3: Patch StorageVarDecl wrapper
- Statement: `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` completes without cheat.
- Approach: Replace the failing `by simp[]` leaf equation with explicit assertions using C3.1.7.1.3.1 and C3.1.7.1.3.2, then call `assign_target_TopLevelVar_Value_branch_ntr`.
- Dependencies: C3.1.7.1.3.1, C3.1.7.1.3.2
- Risk: 1
- Checkpoint: no
- Not to try: do not rely on `drule_all` to invent the leaf facts.

### C3.1.7.2: HashMapRef branch
- Statement: existing `top_level_HashMapRef_assign_no_type_error` remains proved and usable.
- Approach: In parent, extract HashMap declaration/slot witnesses and call it.
- Dependencies: none
- Risk: 1
- Checkpoint: no
- Not to try: do not unfold HashMap assignment in parent.

### C3.1.7.3: ArrayRef branch
- Statement: existing `assign_target_TopLevelVar_ArrayRef_branch_no_type_error` remains proved and usable.
- Approach: In parent ArrayTV case, derive `lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef` then call the boundary theorem.
- Dependencies: none
- Risk: 1
- Checkpoint: no
- Not to try: do not force ArrayTV through the non-array StorageVarDecl lemma.

### C3.1.7.4: Remaining constructors/integration
- Statement: all remaining constructor cases in `sound_TopLevelVar` close.
- Approach: Non-array root type constructors use the StorageVarDecl boundary; ArrayTV uses ArrayRef; HashMapT uses HashMapRef.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3
- Risk: 2
- Checkpoint: no
- Not to try: no broad evaluator unfolding.

## Dependency Graph

`C3.1.7.1.3.1 → C3.1.7.1.3.2 → C3.1.7.1.3.3 → C3.1.7.1 → C3.1.7.4 → C3.1.7`.

`C3.1.7.2` and `C3.1.7.3` are existing boundary dependencies feeding `C3.1.7.4` and then `C3.1.7`.

## Notes

- E0041 is resolved by supersession: do not spend effort repairing the old direct proof episode.
- Stay inside this subtree. Do not plan `sound_ImmutableVar`, `sound_TupleTargetV`, or `sound_assign_targets_cons` here; those are siblings outside this augment scope.
- Since this is an augment of dotted component `C3.1.7`, `required_for_completion` is intentionally false in the structured metadata even though this subtree is task-critical through its parent plan.
- If C3.1.7.1.3.1 fails, escalate with the exact remaining assumptions/goals. That would indicate either the StorageVarDecl adapter needs a stronger hypothesis already present in the wrapper, or the path bridge theorem has a side condition not captured above.

## Structured Components

### C3: C3
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.1.3.1 risk 2. All assumptions are already present in the StorageVarDecl boundary theorem, and the result follows by one application of the target-path-to-place-leaf bridge plus a controlled unfold of `place_leaf_typed_def`/`place_leaf_path_typed_def`.
- Required for completion: yes

### C3.1: C3.1
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.1.3.1 risk 2. All assumptions are already present in the StorageVarDecl boundary theorem, and the result follows by one application of the target-path-to-place-leaf bridge plus a controlled unfold of `place_leaf_typed_def`/`place_leaf_path_typed_def`.

### C3.1.7: TopLevelVar branch of assign_target_sound_mutual via decomposed boundary lemmas
- Kind: `proof_integration`
- Risk: 2
- Rationale: The direct metis-heavy proof episode E0041 is no longer the proof architecture. The branch now reduces by cases on the top-level vtype and calls already-localized boundary lemmas; the only active missing fact is a small adapter from target_path_type/StorageVarDecl to the exact leaf evaluate_type equation needed by the Value boundary lemma.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3, C3.1.7.4
- Checkpoint: yes
- Supersedes: E0041

#### Description
Replace/finish the old direct `assign_target_sound_mutual[sound_TopLevelVar]` attempt with the decomposed branch proof already present around lines 2550--2608. E0041 should be considered abandoned as superseded, not repaired in place by more pair-destructuring/metis search.

#### Statement
`Resume assign_target_sound_mutual[sound_TopLevelVar]: ... QED` with no `cheat`, proving both state-well-typed preservation and no-TypeError for `TopLevelVar`.

#### Approach
Keep the existing structure: first discharge the state-well-typed conjunct using `assign_target_preserves_state_well_typed_mutual`; then case split `tgt`, simplify to `target_runtime_typed_def`, `target_value_shape_def`, and `location_runtime_typed_def`; derive `env.type_defs = get_tenv cx` from `runtime_consistent`; case split `vt`. For `Type t`, extract the storage declaration and root evaluated type from `assign_target_assignable_context`, then dispatch non-array root type constructors to `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` and the `ArrayTV` constructor to `assign_target_TopLevelVar_ArrayRef_branch_no_type_error`. For `HashMapT kt vt`, derive the HashMapVarDecl and slot witnesses and call `top_level_HashMapRef_assign_no_type_error`.

#### Not to try
Do not revive the old direct proof with large `metis_tac` calls over the whole `assign_target_def` expansion; that is E0041 and is superseded. Do not use `DISCH_THEN` instrumentation in new proofs in this file, since holbuild currently blocks `drule`/`irule`/`metis_tac` resolution inside those instrumented continuations.

### C3.1.7.1: Type/StorageVarDecl boundary for TopLevelVar
- Kind: `boundary_lemma_cluster`
- Risk: 2
- Rationale: The Value-branch boundary lemma and the StorageVarDecl wrapper are already in source; the only missing piece is making the leaf `evaluate_type` fact explicit instead of hoping `simp[]` discovers it through a long chain of lemmas.
- Dependencies: C3.1.7.1.3

#### Description
Owns the Type/StorageVarDecl side of `TopLevelVar`: when the top-level static vtype is `Type t` and the declaration is a storage variable, assignment cannot produce `TypeError`.

#### Statement
Existing outputs to retain: `assign_target_TopLevelVar_Value_branch_ntr` and `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`.

#### Approach
Leave `assign_target_TopLevelVar_Value_branch_ntr` intact. Patch `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error` by replacing the failing line `... by simp[]` with calls to the adapter lemmas under C3.1.7.1.3. The wrapper then calls the Value boundary lemma exactly as before.

#### Not to try
Do not unfold `assign_target_def` further in the StorageVarDecl wrapper to re-prove the Value branch inline. The point of this component is to keep the Type branch proof at the lookup-global boundary.

### C3.1.7.1.3: Adapter from Type StorageVarDecl target path to active leaf evaluate_type facts
- Kind: `infrastructure_lemma_cluster`
- Risk: 2
- Rationale: The required facts follow deterministically from already-proved lemmas: `top_level_Type_storage_decl`, `top_level_vtype_well_formed`, `target_path_type_Type_place_leaf_typed`, `place_leaf_typed_evaluate_type` or a direct unfold of `place_leaf_typed_def`/`place_leaf_path_typed_def`, and `assignable_type_evaluate_not_NoneTV`. Splitting the adapter into two facts avoids brittle search in the caller.
- Dependencies: C3.1.7.1.3.1, C3.1.7.1.3.2, C3.1.7.1.3.3

#### Description
This is the active leaf blocker reported in the escalation. It supplies the exact `evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))` fact and the non-`NoneTV` side condition needed by `assign_target_TopLevelVar_Value_branch_ntr`.

#### Statement
Cluster output: a pair of small lemmas, one for the leaf `evaluate_type` equation and one for the leaf non-`NoneTV` side condition, then a caller patch using them.

#### Approach
Prove the equation lemma first. From `top_level_Type_storage_decl`, derive `typ = t`. From `top_level_vtype_well_formed`, derive `well_formed_vtype env.type_defs (Type t)`. Apply `target_path_type_Type_place_leaf_typed` to obtain `?final_tv. place_leaf_typed env (Type t) sbs ty final_tv`. Unfold only `place_leaf_typed_def` and the `Type` case of `place_leaf_path_typed_def` to expose `evaluate_type env.type_defs t = SOME base_tv`, `final_tv = leaf_type base_tv (REVERSE sbs)`, and `evaluate_type env.type_defs ty = SOME final_tv`; use `env.type_defs = get_tenv cx`, `typ = t`, and `evaluate_type (get_tenv cx) typ = SOME root_tv` to identify `base_tv = root_tv`. Then prove non-None by applying `assignable_type_evaluate_not_NoneTV` to the equation lemma. In all proofs, use `rpt strip_tac`, explicit `by (...)` assertions, `drule_all`/`irule`, and `gvs`; avoid `DISCH_THEN`.

#### Not to try
Do not expect `simp[]` alone to find the chain through `target_path_type_Type_place_leaf_typed` and `place_leaf_*` definitions. Do not use a single `metis_tac` with all six lemmas as the primary proof; it is exactly the brittle resolution shape that caused E0041-style failure.

### C3.1.7.1.3.1: Leaf evaluate_type equation for Type StorageVarDecl TopLevelVar
- Kind: `infrastructure_lemma`
- Risk: 2
- Rationale: All assumptions are already present in the StorageVarDecl boundary theorem, and the result follows by one application of the target-path-to-place-leaf bridge plus a controlled unfold of `place_leaf_typed_def`/`place_leaf_path_typed_def`.

#### Statement
Add near the other TopLevelVar helper lemmas:

```sml
Theorem TopLevelVar_Type_StorageVarDecl_leaf_evaluate_type:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) /\
  target_path_type env (Type t) sbs (Type ty) /\
  env.type_defs = get_tenv cx /\
  get_module_code cx src_id_opt = SOME code /\
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) /\
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))
```

#### Approach
After stripping, assert `typ = t` using `top_level_Type_storage_decl`. Assert `well_formed_vtype env.type_defs (Type t)` using `top_level_vtype_well_formed`. Obtain `?final_tv. place_leaf_typed env (Type t) sbs ty final_tv` by `irule`/`drule_all target_path_type_Type_place_leaf_typed`. Then unfold `place_leaf_typed_def` and `place_leaf_path_typed_def` for `Type t`; the exposed base evaluation equals the storage root evaluation by `env.type_defs = get_tenv cx` and `typ = t`, so `gvs[]` should rewrite `base_tv` to `root_tv` and close.

#### Not to try
Do not include `assignable_type` in this equation lemma unless the proof needs it; keeping it out prevents the adapter from depending on assignability for a fact that is purely path-typing.

### C3.1.7.1.3.2: Leaf type is not NoneTV for assignable Type StorageVarDecl path
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: This is a direct corollary of C3.1.7.1.3.1 and the existing `assignable_type_evaluate_not_NoneTV`.
- Dependencies: C3.1.7.1.3.1

#### Statement
```sml
Theorem TopLevelVar_Type_StorageVarDecl_leaf_not_NoneTV:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) /\
  target_path_type env (Type t) sbs (Type ty) /\
  assignable_type (get_tenv cx) ty /\
  env.type_defs = get_tenv cx /\
  get_module_code cx src_id_opt = SOME code /\
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) /\
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  leaf_type root_tv (REVERSE sbs) <> NoneTV
```

#### Approach
Use C3.1.7.1.3.1 to assert the exact `evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))`. Rewrite `env.type_defs = get_tenv cx`, then apply `assignable_type_evaluate_not_NoneTV`.

#### Not to try
Do not unfold `assignable_type`; the existing theorem is the intended boundary.

### C3.1.7.1.3.3: Patch StorageVarDecl boundary caller to use leaf adapter facts
- Kind: `proof_patch`
- Risk: 1
- Rationale: Once the two adapter lemmas exist, the failing caller line becomes two explicit assertions followed by the already-proved Value branch lemma.
- Dependencies: C3.1.7.1.3.1, C3.1.7.1.3.2

#### Statement
Patch inside `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`, Value subcase:

```sml
`evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))` by ...;
`leaf_type root_tv (REVERSE sbs) <> NoneTV` by ...;
drule_all assign_target_TopLevelVar_Value_branch_ntr >> ...
```

#### Approach
Replace the current `... by simp[]` assertion at line ~2485 with an explicit call to `TopLevelVar_Type_StorageVarDecl_leaf_evaluate_type`. Add a second assertion using `TopLevelVar_Type_StorageVarDecl_leaf_not_NoneTV` if it is not already in the goal context; this matches the hypotheses of `assign_target_TopLevelVar_Value_branch_ntr`. Keep the existing `lookup_global_*` contradiction branches unchanged.

#### Not to try
Do not rely on `drule_all assign_target_TopLevelVar_Value_branch_ntr` to synthesize the leaf equation or non-None side condition internally; provide them as assumptions first.

### C3.1.7.2: HashMapRef branch boundary for TopLevelVar
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: `top_level_HashMapRef_assign_no_type_error` is already proved in the gathered source. The TopLevelVar branch only needs to call it after extracting existing witnesses from `assign_target_assignable_context`.

#### Statement
Existing theorem:

```sml
top_level_HashMapRef_assign_no_type_error
```

#### Approach
No redesign. In the parent integration, after the `HashMapT kt vt` case, derive `well_formed_vtype`, use `top_level_HashMap_decl` and the layout witness from `assign_target_assignable_context`, then call this theorem. If the build shows this theorem has regressed, treat it as a local proof repair inside this component, not as a reason to reopen E0041.

#### Not to try
Do not prove HashMapRef by unfolding `assign_target_def` in the parent mutual branch; keep it behind the boundary theorem.

### C3.1.7.3: ArrayRef branch boundary for TopLevelVar Type storage arrays
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: `assign_target_TopLevelVar_ArrayRef_branch_no_type_error` is already present and is called only in the `ArrayTV` root type case after `lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef`.

#### Statement
Existing theorem:

```sml
assign_target_TopLevelVar_ArrayRef_branch_no_type_error
```

#### Approach
No new theorem is required unless holbuild shows this existing theorem contains a cheat or no longer proves. The parent should derive the array lookup fact with `lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef`, then dispatch by `assign_target_TopLevelVar_ArrayRef_branch_no_type_error`.

#### Not to try
Do not route ArrayTV through the non-array StorageVarDecl lemma; that lemma intentionally assumes `(!elem_tv bd. root_tv <> ArrayTV elem_tv bd)`.

### C3.1.7.4: Remaining Type constructors and HashMapT integration in TopLevelVar branch
- Kind: `proof_integration`
- Risk: 2
- Rationale: After C3.1.7.1 is repaired, the remaining constructors are straightforward constructor splits on `root_tv`, but some witness extraction from `assign_target_assignable_context_def` is syntactically delicate.
- Dependencies: C3.1.7.1, C3.1.7.2, C3.1.7.3

#### Statement
The body of `Resume assign_target_sound_mutual[sound_TopLevelVar]` has no `cheat` and no unresolved cases.

#### Approach
For `root_tv = BaseTV/TupleTV/StructTV/FlagTV/NoneTV`, call `assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error`; the universal non-array hypothesis is immediate by constructor discrimination. For `root_tv = ArrayTV elem bd`, first derive the lookup-global ArrayRef fact and call `assign_target_TopLevelVar_ArrayRef_branch_no_type_error`. For `vt = HashMapT kt vt`, use the already-proved HashMap boundary. Prefer explicit assertions for code/declaration/slot/evaluate_type witnesses rather than one large `metis_tac`.

#### Not to try
Do not use `gvs[assign_target_def]` in the parent after the vtype split. If a goal survives a boundary theorem call, it means a boundary hypothesis was not explicitly derived; derive that hypothesis rather than expanding the evaluator.

---

## PLAN AUGMENT: C3.1.7.3 @ 2026-05-14T16:02:35+00:00

# PLAN: C3.1.7.3 — finish the TopLevelVar ArrayRef no-TypeError branch

## Argument

The ArrayRef case of top-level assignment is sound because `resolve_array_element` reduces the surface top-level array target to a concrete storage slot, a concrete leaf type `final_tv`, and the remaining subscripts. The already-proved local facts `resolve_array_element_leaf_type_sc`, `resolve_array_element_ArrayTV_empty_rsubs_sc`, and `resolve_array_element_well_formed_sc` provide the needed consumer boundary: static target-path typing agrees with `leaf_type final_tv remaining_subs`, dynamic-array leaves have no remaining subscripts, and the resolved leaf type is well formed.

Once resolution succeeds, there are only three semantic shapes:

1. Ordinary assignment path: read current storage value, apply `assign_subscripts`, write back the typed new value, then call `assign_result`. Existing lemmas rule out TypeError at each stage.
2. AppendOp on storage dynamic array: check capacity, write the new element, write the incremented length, return `NONE`. Element typing comes from `assign_operation_runtime_typed`; length typing is the small `UintT 256` arithmetic fact below.
3. PopOp on storage dynamic array: check non-empty, read last element, write default value, write decremented length, return `SOME popped`. Existing read/default/write helpers plus the length arithmetic fact rule out TypeError.

If `resolve_array_element` fails, `resolve_array_element_error_sc` says the error is an `Error _`; case analysis and `no_type_error_result_def` close it.

The escalation shows not to use one broad `gvs[AllCaseEqs()]`: generated names destroy the equation shapes expected by the helper lemmas. Factor the proof into boundary lemmas that keep intermediate equations named.

## Definition Design

No definition changes are needed.

- `assign_target_def` has the right computational split. Unfold it once only inside focused branch lemmas.
- `resolve_array_element_def` is already abstracted by the three `_sc` lemmas. Consumers should not unfold it.
- `assign_operation_runtime_typed_def` gives element typing for `AppendOp` and identifies dynamic-array target types for `AppendOp`/`PopOp`.
- `value_has_type_def` gives the concrete `UintT 256` arithmetic obligation for storage-array length writes.

Boundary lemmas to add/use: ordinary ArrayRef no-TypeError, AppendOp dynamic ArrayRef no-TypeError, PopOp dynamic ArrayRef no-TypeError, and local `UintT 256` length-value facts.

Definition probe: C3.1.7.3.2 is the empirical probe. If append length typing cannot be proved from current well-formedness/bounds hypotheses, stop and escalate with the exact residual goal.

Failure signs: if the ordinary boundary lemma still needs generated names from `gvs[AllCaseEqs()]`, its statement is too weak; add explicit named hypotheses. If AppendOp length typing lacks a bound implying `stored_len + 1 < 2 ** 256`, escalate rather than assuming it.

## Code Structure

All edits stay in `semantics/prop/vyperTypeStatePreservationScript.sml`, immediately above `assign_target_TopLevelVar_ArrayRef_branch_no_type_error`. Mark new helper lemmas `[local]` unless export/signature constraints require otherwise. Do not move anything to a shared library.

Keep the existing `resolve_array_element_*_sc` lemmas. Replace the failing inline `TRY (...)` and the two `FAIL_TAC` probes in `assign_target_TopLevelVar_ArrayRef_branch_no_type_error` with dispatch to the new boundary lemmas.

## Components

### C3.1.7.3: Finish ArrayRef TopLevelVar no-TypeError branch
- Statement: prove current `assign_target_TopLevelVar_ArrayRef_branch_no_type_error`.
- Approach: derive existing resolver facts, split on resolved `final_tv`/operation shape, and call ordinary/append/pop boundary lemmas; keep resolve-error path via `resolve_array_element_error_sc`.
- Dependencies: C3.1.7.3.1, C3.1.7.3.2, C3.1.7.3.3, C3.1.7.3.4
- Risk: 2
- Checkpoint: yes
- Not to try: broad `gvs[AllCaseEqs()]`; weakening assignment soundness.

### C3.1.7.3.1: Ordinary ArrayRef boundary lemma
- Statement: prove a local lemma for non-special read/assign_subscripts/write/assign_result path after successful `resolve_array_element`.
- Approach: unfold `assign_target_def` once, preserve named equations, split read/subassign/write in order, and apply existing no-TypeError/type-preservation lemmas.
- Dependencies: none
- Risk: 2
- Checkpoint: no

### C3.1.7.3.2: UintT-256 length-value lemmas
- Statement: prove local `value_has_type (BaseTV (UintT 256))` facts for `IntV &(stored_len + 1)` and `IntV &(stored_len - 1)` under branch hypotheses.
- Approach: unfold `value_has_type_def`; use check hypotheses plus word bounds/well-formed dynamic-array bounds.
- Dependencies: none
- Risk: 1
- Checkpoint: no

### C3.1.7.3.3: AppendOp dynamic ArrayRef boundary lemma
- Statement: prove local lemma for storage dynamic-array AppendOp branch.
- Approach: use `assign_operation_runtime_typed_def` for element typing; C3.1.7.3.2 for length typing; close write errors with `write_storage_slot_no_type_error_from_value_has_type`.
- Dependencies: C3.1.7.3.2
- Risk: 2
- Checkpoint: no

### C3.1.7.3.4: PopOp dynamic ArrayRef boundary lemma
- Statement: prove local lemma for storage dynamic-array PopOp branch.
- Approach: use `read_storage_slot_error`, `default_value_has_type`, C3.1.7.3.2, and `write_storage_slot_no_type_error_from_value_has_type`.
- Dependencies: C3.1.7.3.2
- Risk: 2
- Checkpoint: no

## Dependency Graph

C3.1.7.3.2 → C3.1.7.3.3 and C3.1.7.3.4. C3.1.7.3.1, C3.1.7.3.3, and C3.1.7.3.4 → C3.1.7.3.

## Notes

Stay inside this subtree. Do not edit `sound_TopLevelVar`, `top_level_HashMapRef_assign_no_type_error`, `sound_ImmutableVar`, `sound_TupleTargetV`, or `sound_assign_targets_cons` as part of this component. If append length typing is false under current definitions, report the exact checked residual; that would require broader redesign and should not be patched locally.

## Structured Components

### C3: C3
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.3.1 risk 2. This is the same semantic pattern already proved for `assign_target_TopLevelVar_Value_branch_ntr` and `assign_target_HashMapRef_branch_no_type_error`: read a typed value, assign_subscripts preserves type/no-TypeError, write typed value, then assign_result no-TypeError. The main risk is only statement-shaping to keep named equations.
- Required for completion: yes

### C3.1: C3.1
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.3.1 risk 2. This is the same semantic pattern already proved for `assign_target_TopLevelVar_Value_branch_ntr` and `assign_target_HashMapRef_branch_no_type_error`: read a typed value, assign_subscripts preserves type/no-TypeError, write typed value, then assign_result no-TypeError. The main risk is only statement-shaping to keep named equations.

### C3.1.7: C3.1.7
- Kind: `proof`
- Risk: 2
- Rationale: Derived from child component C3.1.7.3.1 risk 2. This is the same semantic pattern already proved for `assign_target_TopLevelVar_Value_branch_ntr` and `assign_target_HashMapRef_branch_no_type_error`: read a typed value, assign_subscripts preserves type/no-TypeError, write typed value, then assign_result no-TypeError. The main risk is only statement-shaping to keep named equations.

### C3.1.7.3: Finish ArrayRef TopLevelVar no-TypeError branch
- Kind: `proof_subtree`
- Risk: 2
- Rationale: The remaining failure is proof-structural, not mathematical: successful resolve_array_element already yields leaf/remaining-subscript facts; storage read/write helpers already rule out TypeError; AppendOp/PopOp only need small UintT-256 length-value facts. Boundary lemmas avoid the auto-generated-variable matching failure seen after broad gvs[AllCaseEqs()].
- Dependencies: C3.1.7.3.1, C3.1.7.3.2, C3.1.7.3.3, C3.1.7.3.4
- Checkpoint: yes

#### Description
Replace the current failing inline proof of `assign_target_TopLevelVar_ArrayRef_branch_no_type_error` in `vyperTypeStatePreservationScript.sml` with calls to focused ArrayRef boundary lemmas. This component remains strictly within the existing ArrayRef branch helper theorem and its local prerequisites.

#### Statement
```sml
Theorem assign_target_TopLevelVar_ArrayRef_branch_no_type_error:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) ==>
  target_path_type env (Type t) sbs (Type ty) ==>
  assignable_type (get_tenv cx) ty ==>
  assign_operation_runtime_typed env ty op ==>
  env.type_defs = get_tenv cx ==>
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV elem_tv bd) ==>
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (ArrayRef is_transient (n2w slot) elem_tv bd), st) ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```

#### Approach
Keep the existing front matter: derive `typ = t`, `well_formed_type_value (ArrayTV elem_tv bd)`, `evaluate_type env.type_defs ty = SOME (leaf_type (ArrayTV elem_tv bd) (REVERSE sbs))`, and non-None leaf. Then case-split `resolve_array_element`. For `INL (elem_slot, final_tv, remaining_subs)`, derive the existing `_sc` facts and dispatch to: ordinary read/assign_subscripts/write/assign_result boundary; AppendOp dynamic-array boundary; PopOp dynamic-array boundary. For the `INR` resolve case, retain `resolve_array_element_error_sc`.

#### Not to try
Do not continue expanding the whole `assign_target` branch with `gvs[AllCaseEqs()]` and then try positional `metis_tac`/`irule`; the escalated evidence shows generated names lose the expected equation shape. Do not weaken assignment soundness side conditions.

### C3.1.7.3.1: Ordinary ArrayRef read/write/assign_result boundary lemma
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: This is the same semantic pattern already proved for `assign_target_TopLevelVar_Value_branch_ntr` and `assign_target_HashMapRef_branch_no_type_error`: read a typed value, assign_subscripts preserves type/no-TypeError, write typed value, then assign_result no-TypeError. The main risk is only statement-shaping to keep named equations.

#### Statement
Add a local/helper theorem just above `assign_target_TopLevelVar_ArrayRef_branch_no_type_error`, named for example:

```sml
Theorem assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error[local]:
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (ArrayRef is_transient base_slot elem_tv bd), st) ==>
  resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) (REVERSE sbs) st =
    (INL (elem_slot, final_tv, remaining_subs), st_res) ==>
  (op = PopOp ==> !pop_elem_tv n. final_tv <> ArrayTV pop_elem_tv (Dynamic n)) ==>
  (!v app_elem_tv n. op = AppendOp v ==> final_tv <> ArrayTV app_elem_tv (Dynamic n)) ==>
  well_formed_type_value final_tv ==>
  assign_operation_runtime_typed env ty op ==>
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining_subs) ==>
  leaf_type final_tv remaining_subs <> NoneTV ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
```

#### Approach
Unfold `assign_target_def` once only far enough to expose the assumed successful `lookup_global` and `resolve_array_element`. Case-split named calls in order: `read_storage_slot`, `assign_subscripts`, `write_storage_slot`. Use `read_storage_slot_error`, `read_storage_slot_success_type`, `assign_subscripts_no_type_error_runtime_typed`, `assign_subscripts_preserves_type_runtime_typed`, `write_storage_slot_no_type_error_from_value_has_type`, and `assign_result_no_type_error_from_successful_assign` or `_split`. The exclusion hypotheses ensure special dynamic-array Append/Pop branches are not selected.

#### Not to try
Do not use a `TRY (gvs[AllCaseEqs()] >> rpt FIRST [...])` block here; keep intermediate equations named.

### C3.1.7.3.2: UintT-256 length values for storage dynamic-array length writes
- Kind: `infrastructure_lemma`
- Risk: 1
- Rationale: Both facts reduce directly to `value_has_type_def` for `BaseTV (UintT 256)` plus arithmetic from the storage-array checks and word bounds/well-formed dynamic-array bounds.

#### Statement
Add one or two small local lemmas, choosing the exact hypotheses that match the branch context:

```sml
Theorem storage_array_append_len_value_has_type[local]:
  stored_len < n ==>
  n <= 2 ** 256 ==>
  value_has_type (BaseTV (UintT 256)) (IntV (&(stored_len + 1)))

Theorem storage_array_pop_len_value_has_type[local]:
  stored_len > 0 ==>
  stored_len < 2 ** 256 ==>
  value_has_type (BaseTV (UintT 256)) (IntV (&(stored_len - 1)))
```

If the branch has `stored_len = w2n (lookup_storage elem_slot storage)`, the pop bound can be derived using word `w2n` bounds rather than passed as a hypothesis.

#### Approach
Prove by `simp[value_has_type_def]` and arithmetic. For append, derive `stored_len + 1 < 2 ** 256` from `stored_len < n` plus the dynamic-array bound present after unfolding `well_formed_type_value_def` for `ArrayTV app_elem_tv (Dynamic n)`. For pop, use `stored_len > 0` and the word-bound/source bound to show `stored_len - 1 < 2 ** 256`.

#### Not to try
Do not prove these by unfolding `write_storage_slot`; they are value-typing facts needed before applying `write_storage_slot_no_type_error_from_value_has_type`. If append lacks any bound implying `stored_len + 1 < 2 ** 256`, escalate with the exact residual goal.

### C3.1.7.3.3: AppendOp dynamic ArrayRef no-TypeError boundary lemma
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: After resolving to a dynamic array leaf, the AppendOp branch performs a bounds check and two writes. The append value is typed by `assign_operation_runtime_typed`; the length write is typed by C3.1.7.3.2; check failure is not TypeError.
- Dependencies: C3.1.7.3.2

#### Statement
Add a local/helper theorem, for example:

```sml
Theorem assign_target_TopLevelVar_ArrayRef_append_no_type_error[local]:
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (ArrayRef is_transient base_slot elem_tv bd), st) ==>
  resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) (REVERSE sbs) st =
    (INL (elem_slot, ArrayTV app_elem_tv (Dynamic n), []), st_res) ==>
  well_formed_type_value (ArrayTV app_elem_tv (Dynamic n)) ==>
  assign_operation_runtime_typed env ty (AppendOp v) ==>
  evaluate_type env.type_defs ty = SOME (ArrayTV app_elem_tv (Dynamic n)) ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) (AppendOp v) st = (res, st') ==>
  no_type_error_result res
```

#### Approach
Unfold to the resolved ArrayRef AppendOp branch. Expose `get_storage_backend`, `lookup_storage`, and the `check (stored_len < n)` result. If the check fails, close by `no_type_error_result_def`. If it succeeds, case-split the first `write_storage_slot`; contradict TypeError using `write_storage_slot_no_type_error_from_value_has_type` and `value_has_type app_elem_tv v` from `assign_operation_runtime_typed_def`. For the second length write, use C3.1.7.3.2 and `write_storage_slot_no_type_error_from_value_has_type`. Successful writes close by simplification.

#### Not to try
Do not use `assign_subscripts_no_type_error_runtime_typed`; storage dynamic-array AppendOp bypasses `assign_subscripts`.

### C3.1.7.3.4: PopOp dynamic ArrayRef no-TypeError boundary lemma
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The PopOp branch performs a non-empty check, typed read, default-value write, and length write. Existing helpers cover read errors, default-value typing, and typed writes; C3.1.7.3.2 covers the decremented length value.
- Dependencies: C3.1.7.3.2

#### Statement
Add a local/helper theorem, for example:

```sml
Theorem assign_target_TopLevelVar_ArrayRef_pop_no_type_error[local]:
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (ArrayRef is_transient base_slot elem_tv bd), st) ==>
  resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) (REVERSE sbs) st =
    (INL (elem_slot, ArrayTV pop_elem_tv (Dynamic n), []), st_res) ==>
  well_formed_type_value (ArrayTV pop_elem_tv (Dynamic n)) ==>
  assign_operation_runtime_typed env ty PopOp ==>
  evaluate_type env.type_defs ty = SOME (ArrayTV pop_elem_tv (Dynamic n)) ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) PopOp st = (res, st') ==>
  no_type_error_result res
```

#### Approach
Unfold to the PopOp branch. If `check (stored_len > 0)` fails, simplify. If it succeeds, case-split `read_storage_slot`; `INR` closes via `read_storage_slot_error`. On read success, case-split the default-value write; contradict TypeError using `default_value_has_type` and `write_storage_slot_no_type_error_from_value_has_type`. Then case-split the length write; use C3.1.7.3.2 and `write_storage_slot_no_type_error_from_value_has_type`. Successful path returns `SOME popped`, so `simp[no_type_error_result_def]` closes.

#### Not to try
Do not prove broader preservation or popped-value typing here; this subtree only needs no-TypeError.
