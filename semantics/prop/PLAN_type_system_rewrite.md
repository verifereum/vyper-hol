# PLAN: Complete the fresh Vyper type-system soundness rewrite

## Argument

The fresh stack should prove soundness by the strongest joint invariant that follows each evaluator recursion. For assignment targets, the key joint theorem is `assign_target_sound_mutual`: from `runtime_consistent`, target runtime typing, assignability of the target type, operation runtime typing, operation/target shape compatibility, and runtime assignable context, every `assign_target`/`assign_targets` result preserves runtime consistency and cannot be `Error (TypeError s)`. This theorem is intentionally stronger than legacy no-TypeError wrappers because assignment can partially update state before later failure; the all-result invariant is what lets list/tuple assignment continue soundly through intermediate states.

The current lynchpin is completing the remaining branches of `assign_target_sound_mutual`. Top-level storage `Value` is already proved; the remaining top-level `HashMapRef` and `ArrayRef` cases should be isolated behind exact branch helpers that connect runtime references to static declarations/layout and then reduce suffix assignment to the recursive subscript theorems. Immutable, tuple, and list-cons cases then use the same strengthened predicates (`assign_operation_matches_target_shape`, `assign_target_assignable_context`, `target_assignment_values_assignable`) rather than reconstructing evaluator logic.

Statement assignment cases must not inspect `assign_target_def`. They first evaluate the target/RHS, derive the strengthened assignment premises from statement typing, target typing, runtime consistency, assignability preservation, and `assignable_type`; then they call the joint assignment theorem or a compatibility wrapper. Builtin/binop obligations are localized prerequisites for expression soundness and update assignment. Call and public wrappers are projections/setup lemmas over the completed statement/callable-body joint invariant. Final completion is exactly the TASK criterion: `holbuild build vyperSemanticsHolTheory` succeeds with zero reachable CHEAT warnings and the public fresh wrappers retain the frozen behavior.

## Definition Design

### Existing `assign_target_sound_mutual` interface
- Purpose: the central all-result assignment invariant: no TypeError and runtime consistency preservation for both single targets and target lists.
- Shape: recursion-matching induction on `assign_target_ind`; first conjunct for `assign_target`, second for `assign_targets`. The list conjunct is deliberately stated over the real state before the list assignment and must be used on the intermediate state after the head assignment.
- Boundary: consumers use `assign_target_sound_mutual` or wrappers from `vyperTypeAssignSoundnessScript.sml`; statement proofs should not unfold `assign_target_def`.
- Probes: C3.1/C3.2 exact top-level reference helpers and C3.5 list-cons branch test whether the strengthened side conditions are sufficient.
- Failure signs: needing additional statement-level assumptions in the mutual theorem, or inability to re-establish tail list premises after the head assignment.

### Existing `assign_target_assignable_context`
- Purpose: names runtime writability/assignability, including scoped assignability and top-level declaration/layout/hashmap storage witnesses.
- Shape: structural over evaluated target values; tuple targets lift componentwise; top-level variables require module code/declaration/layout evidence, and hashmaps require nonempty subscript/path evidence.
- Boundary: top-level branch helpers may unfold it; statement proofs should use C5.2 lemmas deriving it from typing/evaluation/runtime consistency.
- Probes: C3.1/C3.2 show sufficiency for `HashMapRef`/`ArrayRef`; C5.2 shows derivability from statement-level hypotheses.
- Failure signs: top-level statement cases cannot derive layout or nonempty-subscript witnesses. Escalate with the residual goal rather than weakening the mutual theorem.

### Existing `assign_operation_matches_target_shape`
- Purpose: names compatibility between an evaluated target value and the requested assignment operation, especially tuple replacement shape.
- Shape: finite case split on target value and operation; base targets are simple, tuple targets force replacement with aligned component values.
- Boundary: use operation-specific C5.1 lemmas in statement proofs; tuple branch of C3 may unfold directly.
- Probes: C3.4 and C5.1.
- Failure signs: tuple branches require ad hoc `EL`/index reasoning instead of list-relation/length facts.

### Existing `target_assignment_values_assignable`
- Purpose: packages componentwise target typing, RHS/materialized value typing, and assignability/context facts for tuple/list assignment.
- Shape: list relation matching `assign_targets` recursion.
- Boundary: tuple/list statement cases use C5.4 packaging lemmas; assignment-target mutual uses the predicate directly.
- Probes: C3.4/C3.5 and C5.4.
- Failure signs: after assigning the head, tail premises cannot be transported to the intermediate state; this means a preservation/context stability lemma is missing.

### Existing `assignable_type`
- Purpose: static exclusion of `NoneT`, recursively through aggregate assignable types.
- Shape: recursive over type syntax, with boundary facts already present: `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV`.
- Boundary: AnnAssign/materialization proofs use C5.3 helpers and these theorems; do not add local non-None assumptions.
- Probes: C5.3.
- Failure signs: AnnAssign still needs a non-None fact not derivable from `assignable_type` and type evaluation.

### Builtin/binop/type-builtin predicates
- Purpose: connect executable builtin/operator evaluation to internal well-typedness predicates and result typing.
- Shape: finite constructor/case interfaces in `vyperTypeBuiltinsScript.sml`.
- Boundary: downstream files consume no-TypeError and success-type wrappers from C1; they do not unfold builtin semantics.
- Probes: C1.3 ABI/type-builtin probes and C1.1 update-binop proof.
- Failure signs: an internally well-typed builtin branch evaluates to `TypeError`; repair internal typing/runtime alignment if allowed by TASK, or escalate if it reaches frozen public behavior.

## Code Structure

Preserve the current fresh-stack split; do not create replacement old-stack theories.

- `vyperTypeBuiltinsScript.sml`: C1 builtin/binop/type-builtin local no-TypeError and success-typing proofs; internal predicate/runtime repairs only when forced by checked branch evidence.
- `vyperTypeStatePreservationScript.sml`: C2 subscript/leaf helpers and C3 assignment-target mutual branch helpers/resumes.
- `vyperTypeAssignSoundnessScript.sml`: C4 compatibility wrappers only, projected from the joint assignment theorem.
- `vyperTypeStmtSoundnessScript.sml`: C5 statement-level side-condition lemmas and C6/C7 `eval_all_type_sound_mutual` integrations.
- `vyperTypeCallSoundnessScript.sml`: C8 call/callable-body setup lemmas and wrapper projections.
- `vyperTypeSoundnessNewScript.sml`: C9 public theorem surface only; maintain equivalent public behavior.

Retired old theories (`vyperTypeSoundnessDefs`, `vyperTypeSoundnessHelpers`, `vyperTypeSoundness`) are out of scope unless C0 shows they are imported transitively by `vyperSemanticsHolTheory`.

## Components

### C0: Reachability and current-source cheat audit
- Statement: run `holbuild build vyperTypeStatePreservationTheory` and `holbuild build vyperSemanticsHolTheory`; map every reachable cheat/suspend/scaffold to C1–C9.
- Approach: mechanical audit before proof edits.
- Dependencies: none
- Risk: 1
- Checkpoint: yes
- Not to try: repository-wide cleanup or old-stack edits without reachability evidence.

### C1: Localized builtin/binop/type-builtin soundness
- Statement: remove all reachable cheats/suspended branches in `vyperTypeBuiltinsScript.sml`, including binop/update-binop, builtin app, success typing, and type-builtin/ABI obligations.
- Approach: prove finite constructor wrappers; repair internal predicates/runtime support only for checked local mismatches.
- Dependencies: C0
- Risk: 2
- Checkpoint: yes
- Not to try: adding exclusions to public soundness wrappers or unfolding builtin semantics downstream.

### C2: Assignment subscript and leaf-operation soundness
- Statement: remove inherited update-binop path cheats such as `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`.
- Approach: leaf operation first, then recursion-matching induction on `assign_subscripts`; update consumes C1.
- Dependencies: C1
- Risk: 2
- Checkpoint: yes
- Not to try: weakening dynamic-array premises or reproving binops here.

### C3: Complete `assign_target_sound_mutual`
- Statement: finalize the current mutual theorem for `assign_target`/`assign_targets`, replacing the scaffolds for `sound_TopLevelVar` `HashMapRef`, `sound_TopLevelVar` `ArrayRef`, `sound_ImmutableVar`, `sound_TupleTargetV`, and `sound_assign_targets_cons`.
- Approach: exact branch helpers for top-level references; immutable/tuple/list cases consume strengthened predicates and mutual IHs.
- Dependencies: C2
- Risk: 2
- Checkpoint: yes
- Not to try: broad `AllCaseEqs()` cleanup or weakening the strengthened side conditions.

#### C3.1: TopLevelVar HashMapRef branch helper
Use assignable context for nonempty subscripts/layout, declaration facts for returned `HashMapRef`, strengthened hashmap key/path typing for slot computation, C2 for suffix assignment, and storage read/write no-TypeError facts.

#### C3.2: TopLevelVar ArrayRef branch helper
Split append, pop, and ordinary element/path assignment immediately. Dynamic-array facts handle append/pop; ordinary assignment reduces to C2 plus typed storage write-back.

#### C3.3: ImmutableVar branch
Use immutable consistency and setter preservation helpers; C2 handles subscript/leaf operation no-TypeError.

#### C3.4: TupleTargetV branch
Use `assign_operation_matches_target_shape` to force tuple replacement/length alignment and `target_assignment_values_assignable` to invoke `assign_targets`.

#### C3.5: assign_targets cons branch
Apply the head IH to the real intermediate state; use preservation/runtime consistency to re-establish tail premises; then apply the tail IH.

#### C3.6: TopLevelVar resume integration
Keep the proved Value branch and dispatch HashMapRef/ArrayRef to C3.1/C3.2.

### C4: Assignment compatibility wrappers
- Statement: prove reachable wrappers in `vyperTypeAssignSoundnessScript.sml`, including `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error` or current equivalents.
- Approach: project from C3; update callers to supply strengthened premises or use C3 directly.
- Dependencies: C3
- Risk: 2
- Checkpoint: no
- Not to try: a second assignment induction.

### C5: Statement-level assignment side-condition lemmas
- Statement: derive `assign_operation_matches_target_shape`, `assign_target_assignable_context`, AnnAssign non-None facts, and tuple/list `target_assignment_values_assignable` from statement typing/evaluation hypotheses.
- Approach: scoped cases use assignability/env preservation; top-level cases use declaration/layout consistency; AnnAssign uses `assignable_type` lemmas; tuple/list cases package aligned component facts.
- Dependencies: C3, C4
- Risk: 2
- Checkpoint: yes
- Not to try: unfolding `assign_target_def` in statement proofs.

### C6: Assignment statement branches in `eval_all_type_sound_mutual`
- Statement: close assignment-related statement cases, especially `AnnAssign`, `Assign`, `AugAssign`, tuple/list assignment, and append/pop/update assignment branches.
- Approach: follow evaluator order; derive C3 premises via C5 at the assignment invocation; `AugAssign` uses C1/C2.
- Dependencies: C1, C2, C3, C4, C5
- Risk: 2
- Checkpoint: yes
- Not to try: duplicating assignment-target branch logic.

### C7: Remaining statement evaluator mutual cases
- Statement: remove all remaining reachable cheats/suspended cases inside `eval_all_type_sound_mutual` not covered by C6.
- Approach: branch-by-branch within the existing joint invariant, consuming expression soundness, builtin soundness, scope-pop, env-extension/preservation, assignment soundness, and call setup facts as appropriate.
- Dependencies: C1, C6
- Risk: 2
- Checkpoint: yes
- Not to try: parallel no-TypeError-only evaluator proofs.

### C8: Call and callable-body soundness wrappers
- Statement: prove `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, `special_call_no_type_error`, and current callable-body wrappers required by the public surface.
- Approach: use completed statement/callable-body joint soundness plus setup lemmas for defaults, env extension, accounts, signatures, and scope restoration; wrappers are projections.
- Dependencies: C7
- Risk: 2
- Checkpoint: yes
- Not to try: separate call no-TypeError and preservation proof trees.

### C9: Public fresh surface and final zero-CHEAT build
- Statement: maintain wrappers equivalent in strength to the TASK-listed public surface and verify `holbuild build vyperSemanticsHolTheory` with zero reachable CHEAT warnings.
- Approach: projection layer plus final build/audit.
- Dependencies: C4, C7, C8
- Risk: 1
- Checkpoint: yes
- Not to try: weakening frozen public behavior.

## Dependency Graph

C0 gates current-source reachability. C0 → C1 → C2 → C3. Within C3, C3.1 and C3.2 feed C3.6; C3.3, C3.4, and C3.5 complete the other suspended mutual branches. C3 → C4 and C5. C1/C2/C3/C4/C5 → C6. C1/C6 → C7. C7 → C8. C4/C7/C8 → C9.

## Notes

- First proof-editing focus after C0 should be the TASK handover branches in `vyperTypeStatePreservationScript.sml`, especially `TopLevelVar` `HashMapRef` and then `ArrayRef`; however C1/C2 must be completed before any update/subscript path that currently depends on cheated builtin/binop facts can be considered cheat-free.
- If C5 cannot derive `assign_target_assignable_context` for top-level evaluated targets, escalate with the exact residual goal. This is a missing invariant/interface bridge, not permission to weaken `assign_target_sound_mutual`.
- If C1 exposes a concrete internally well-typed builtin that returns `TypeError`, use the TASK's non-frozen internal-helper permission to repair typing/runtime alignment. If the counterexample reaches frozen public behavior, stop and report rather than weakening the public wrappers.
- Old retired theories are context only unless C0 proves reachability from `vyperSemanticsHolTheory`.

## Structured Components

### C0: Reachability and current-source cheat audit
- Kind: `audit`
- Risk: 1
- Rationale: Mechanical holbuild/grep work. It only aligns the execution queue with the TASK criterion and current source; no mathematical uncertainty.
- Checkpoint: yes

#### Statement
Run `holbuild build vyperTypeStatePreservationTheory` and `holbuild build vyperSemanticsHolTheory`; record every `cheat`, `suspend`, or build-through scaffold reachable from `vyperSemanticsHolTheory` in the fresh stack and map it to C1–C9 below.

#### Approach
Use `holbuild` as required by the TASK. Do not include retired theories unless the build/audit shows they are imported transitively by `vyperSemanticsHolTheory`. If a reachable cheat is not covered by C1–C9, stop and ask for a plan augment rather than inventing a new work item.

#### Not to try
Do not do repository-wide cleanup or edit old `vyperTypeSoundness*` theories without reachability evidence.

### C1: Localized builtin/binop/type-builtin soundness
- Kind: `proof_cluster`
- Risk: 2
- Rationale: These obligations are finite constructor/case analyses over builtin/operator/type-builtin typing and runtime definitions. The TASK permits internal helper repair where mismatches such as ABI bounds or `MsgGas` are demonstrated; public behavior must not be weakened.
- Required for completion: yes
- Dependencies: C0
- Checkpoint: yes

#### Statement
Remove all reachable cheats/suspended branches in `semantics/prop/vyperTypeBuiltinsScript.sml`, including current-source obligations such as `well_typed_binop_no_type_error`, `well_typed_binop_success_type`, `well_typed_update_binop_no_type_error`, `well_typed_builtin_app_no_type_error`, `well_typed_builtin_app_success_type`, `well_typed_type_builtin_no_type_error`, and `well_typed_type_builtin_success_type` (or their current-source names).

#### Approach
Prove one local wrapper per builtin family: binops first, then update-binop, builtin app no-TypeError, builtin app success typing, type-builtin no-TypeError, and type-builtin success typing. Each branch should rewrite the executable builtin and typing predicates and use existing value/bytes/crypto/ABI helper lemmas. If a branch exposes a real typing/runtime mismatch, repair the internal typing predicate or runtime support in the smallest file owning that concept, then prove the wrapper; do not add exclusions to the public theorem surface.

#### Not to try
Do not unfold builtin semantics in downstream assignment or statement proofs. Do not add public side conditions forbidding ABI-encode sizes, `MsgGas`, or other builtin cases unless a required frozen public theorem is proved false by a checked counterexample.

### C1.1: Binop and update-binop no-TypeError/success typing
- Kind: `proof`
- Risk: 2
- Rationale: Finite split over operator and operand runtime type cases; it is the root dependency of the assignment update path.
- Dependencies: C0

#### Statement
Prove current-source binop/update-binop obligations, especially `well_typed_binop_no_type_error`, `well_typed_binop_success_type`, and `well_typed_update_binop_no_type_error`.

#### Approach
Induct/case-split by operator and operand value constructors, matching `well_typed_binop_def` and executable binop evaluation. Success typing should be proved alongside no-TypeError where possible so update assignment can consume one coherent interface.

#### Not to try
Do not defer update-binop by cheating assignment subscript lemmas; C2 must be downstream of this component.

### C1.2: Builtin app no-TypeError and success typing
- Kind: `proof`
- Risk: 2
- Rationale: Many branches but each is a local constructor branch; existing helper theories cover bytes, crypto, conversions, defaults, accounts, and ABI values.
- Dependencies: C1.1

#### Statement
Prove all current suspended/cheated branches of `well_typed_builtin_app_no_type_error` and `well_typed_builtin_app_success_type`.

#### Approach
Close the suspended branches one at a time. For crypto/bytes/string/array constructors, use the corresponding fresh helper theory. For account/env branches, prove local environment/account well-typed lookup facts if missing. Keep success typing as a direct consequence of the declared builtin result type predicate.

#### Not to try
Do not create a second general expression soundness theorem in the builtin file.

### C1.3: Type-builtin/ABI bound probes and proofs
- Kind: `proof`
- Risk: 2
- Rationale: The known ABI-size and type-builtin issues are localized. Probes identify whether the source already has repaired predicates such as `vyper_abi_size_bound`; after that, proofs are finite cases.
- Dependencies: C1.1
- Checkpoint: yes

#### Statement
Prove all reachable current-source type-builtin no-TypeError and success-typing obligations, including ABI encode/decode/extract branches.

#### Approach
First prove tiny probe lemmas for the exact ABI branches: the well-typed type-builtin predicate implies any executable bound needed by ABI encode, tuple encode, and nowrap encode. Then prove the full no-TypeError and success-type wrappers by case split on the type-builtin constructor.

#### Not to try
Do not hide an ABI bound as an assumption on public soundness wrappers. If the predicate genuinely lacks the needed bound, repair the internal type-builtin predicate and update callers.

### C2: Assignment subscript and leaf-operation soundness
- Kind: `proof_cluster`
- Risk: 2
- Rationale: The key theorems follow the recursion of `assign_subscripts` once C1 supplies builtin/update-binop soundness. Existing statements already match the strengthened dynamic-array and leaf-type architecture.
- Required for completion: yes
- Dependencies: C1
- Checkpoint: yes

#### Statement
Remove inherited update-binop path cheats reachable through `vyperTypeStatePreservationScript.sml`, including current-source obligations named in the TASK: `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`.

#### Approach
First prove the leaf operation theorem for all assignment operations: replace/update/append/pop. Update consumes C1; append/pop use the strengthened dynamic-array premise in `assign_operation_runtime_typed`. Then prove subscript no-TypeError and preservation by recursion-matching induction on `assign_subscripts`, carrying the evaluated leaf type and `assignable_type`/non-`NoneTV` facts through the suffix.

#### Not to try
Do not weaken `assign_operation_runtime_typed` for `PopOp`; the dynamic-array condition is what makes the branch true. Do not unfold binop semantics here.

### C3: Complete `assign_target_sound_mutual`
- Kind: `mutual_theorem`
- Risk: 2
- Rationale: The theorem has already been strengthened with the necessary side conditions. Remaining branches are local to `vyperTypeStatePreservationScript.sml`; the hardest Value branch is already proved and handover gives exact branch boundaries for HashMapRef/ArrayRef.
- Required for completion: yes
- Dependencies: C2
- Checkpoint: yes

#### Statement
Finalize current-source theorem:
```sml
Theorem assign_target_sound_mutual:
  (!cx gv op st res st'.
    assign_target cx gv op st = (res, st') ==>
    !env tgt ty.
      runtime_consistent env cx st /\
      target_runtime_typed env cx st tgt ty gv /\
      assignable_type env.type_defs ty /\
      assign_operation_runtime_typed env ty op /\
      assign_operation_matches_target_shape gv op /\
      assign_target_assignable_context cx gv st ==>
      runtime_consistent env cx st' /\ no_type_error_result res) /\
  (!cx gvs vs st res st'.
    assign_targets cx gvs vs st = (res, st') ==>
    !env tgts.
      runtime_consistent env cx st /\
      target_assignment_values_assignable env cx st tgts gvs vs /\
      EVERY (\gv. assign_target_assignable_context cx gv st) gvs ==>
      runtime_consistent env cx st' /\ no_type_error_result res)
```
Specifically replace the scaffolding for `sound_TopLevelVar` `HashMapRef`, `sound_TopLevelVar` `ArrayRef`, `sound_ImmutableVar`, `sound_TupleTargetV`, and `sound_assign_targets_cons`.

#### Approach
Keep branch helper lemmas above the mutual resume and dispatch the resume by exact branch helpers. In every branch, prove preservation by `assign_target_preserves_state_well_typed_mutual`/runtime-consistency preservation and prove no-TypeError by the branch-specific no-TypeError lemma. Split semantic cases as the evaluator branches and close each immediately.

#### Not to try
Do not use broad `gvs[..., AllCaseEqs(), ...]` at top level and then clean up dozens of residual goals. Do not weaken `assign_target_sound_mutual` or remove `assign_operation_matches_target_shape`/`assign_target_assignable_context`.

### C3.1: TopLevelVar HashMapRef branch helper
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The source already has decomposition lemmas around `HashMapRef`, `target_path_type_HashMapT_*`, split hashmap subscripts, and storage no-TypeError facts. The helper is an exact consumer-facing lemma for one evaluator branch.
- Dependencies: C2
- Checkpoint: yes

#### Statement
State and prove an exact helper for the branch where `lookup_global cx src n st = (INL (HashMapRef is_transient base_slot kt vt), st)` inside `assign_target cx (BaseTargetV (TopLevelVar src n) sbs) op st`. The conclusion must be the branch's `no_type_error_result res` (and any `runtime_consistent` projection needed by C3) under the same hypotheses supplied to `assign_target_sound_mutual`.

#### Approach
Use `assign_target_assignable_context` to obtain nonempty subscripts and layout/slot witnesses for the top-level hashmap declaration. Use lookup/declaration facts such as `lookup_global_HashMapVarDecl_returns_HashMapRef` or local equivalents plus `top_level_HashMap_decl` to connect the returned `HashMapRef` with `HashMapT kt vt`. Use strengthened `target_path_type` to obtain key well-typedness for the hashmap prefix and a leaf bridge via `split_hashmap_subscripts`; then invoke C2 for suffix assignment. Storage read failures are runtime errors, not type errors; storage write-back no-TypeError follows from the typed written value.

#### Not to try
Do not attempt this inline in `sound_TopLevelVar` before the helper statement compiles. Do not destruct the whole `lookup_global`/`assign_target` computation with global `AllCaseEqs()`.

### C3.2: TopLevelVar ArrayRef branch helper
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: This is a finite split into dynamic-array append, dynamic-array pop, and ordinary element/path update. Existing array-place and storage-write helpers should align with C2.
- Dependencies: C2
- Checkpoint: yes

#### Statement
State and prove exact helpers for the branch where `lookup_global` returns `ArrayRef ...` in `sound_TopLevelVar`, including any current local dynamic-array append/pop helpers.

#### Approach
Split first on assignment operation. Append and pop use dynamic-array facts from `assign_operation_runtime_typed`; ordinary assignment resolves the array element/path, obtains the leaf type for the suffix, calls C2, and then uses typed storage write-back no-TypeError. Preserve state/env/account invariants by the all-result preservation theorem rather than by branch-specific state reasoning.

#### Not to try
Do not reduce array assignment to hashmap helper lemmas; the evaluator branch structure is different.

### C3.3: ImmutableVar branch
- Kind: `proof`
- Risk: 2
- Rationale: No top-level layout/hashmap branch complexity; existing immutable update preservation helpers were factored for this purpose.
- Dependencies: C2

#### Statement
Replace `Resume assign_target_sound_mutual[sound_ImmutableVar]` scaffold with a proof of the immutable target branch of C3.

#### Approach
Use immutable runtime consistency to obtain the current immutable value/type, use C2 for subscript/leaf updates, and use `set_immutable_preserves_env_consistent` and all-result `set_immutable_preserves_state_well_typed` for preservation. No-TypeError is by leaf/subscript no-TypeError plus successful assignment-result no-TypeError.

#### Not to try
Do not treat immutable variables as scoped variables; use the immutable-specific consistency and setter lemmas.

### C3.4: TupleTargetV branch
- Kind: `proof`
- Risk: 2
- Rationale: `assign_operation_matches_target_shape` and `target_assignment_values_assignable` were introduced exactly to make this branch structural instead of ad hoc.
- Dependencies: C2

#### Statement
Replace `Resume assign_target_sound_mutual[sound_TupleTargetV]` scaffold with the tuple target branch of C3.

#### Approach
Unfold only `assign_operation_matches_target_shape_def` and `target_assignment_values_assignable_def` as boundary predicates. The shape predicate should force replacement with component values of matching length; package the componentwise typedness and assignable context into the premises of `assign_targets`. Then apply the second conjunct/IH of C3.

#### Not to try
Do not reconstruct tuple/list alignment by indexing or repeated `EL`; use the list relation in `target_assignment_values_assignable`.

### C3.5: assign_targets cons branch
- Kind: `proof`
- Risk: 2
- Rationale: The only subtlety is transporting tail premises across the state returned by the head assignment; C3's first conjunct and all-result preservation provide exactly that.
- Dependencies: C3.3, C3.4

#### Statement
Replace `Resume assign_target_sound_mutual[sound_assign_targets_cons]` scaffold with the list-cons branch of the second conjunct of C3.

#### Approach
Destructure `LIST_REL3`/`target_assignment_values_assignable` and `EVERY` for head and tail. Apply the head IH to the real intermediate state. From the resulting `runtime_consistent env cx st1`, re-establish the tail premises (including any assignable-context stability needed by the definition), then apply the tail IH. Finish both success and failure result cases with `no_type_error_result_def`.

#### Not to try
Do not prove head and tail against the original state; the evaluator recurses on the post-head state.

### C3.6: TopLevelVar resume integration
- Kind: `integration`
- Risk: 1
- Rationale: After C3.1 and C3.2, the TopLevelVar resume is dispatch over already-proved Value/HashMapRef/ArrayRef branch helpers.
- Dependencies: C3.1, C3.2

#### Statement
Complete `Resume assign_target_sound_mutual[sound_TopLevelVar]` by replacing the remaining `HashMapRef` and `ArrayRef` cheats with calls to C3.1/C3.2 helpers.

#### Approach
Keep the existing proved Value branch. In `HashMapRef` and `ArrayRef` cases, avoid further semantic decomposition and call the exact helper with `goal_assum drule_all`/matching instantiations.

#### Not to try
Do not rewrite the already-proved Value branch.

### C4: Assignment compatibility wrappers
- Kind: `corollary_cluster`
- Risk: 2
- Rationale: Once C3 is final, legacy wrappers are projections or small compatibility corollaries. Risk is limited to supplying the strengthened premises at wrapper call sites or updating callers to use C3 directly.
- Required for completion: yes
- Dependencies: C3

#### Statement
Remove reachable cheats in `semantics/prop/vyperTypeAssignSoundnessScript.sml`, especially `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error` or their current-source equivalents.

#### Approach
Do not re-induct over assignment. Project `no_type_error_result` from `assign_target_sound_mutual`. If old wrappers have weaker premises, either strengthen the wrapper internally and update all fresh-stack callers, or prove a compatibility corollary only when its old premises genuinely imply `assign_operation_matches_target_shape` and `assign_target_assignable_context`.

#### Not to try
Do not duplicate evaluator case analysis from `assign_target`.

### C5: Statement-level assignment side-condition lemmas
- Kind: `infrastructure_lemma_cluster`
- Risk: 2
- Rationale: The TASK identifies these side conditions as the exact blocker. They are structural consequences of statement typing, target evaluation, assignability preservation, and top-level declaration/layout consistency.
- Required for completion: yes
- Dependencies: C3, C4
- Checkpoint: yes

#### Statement
In `vyperTypeStmtSoundnessScript.sml`, prove reusable lemmas deriving:
1. `assign_operation_matches_target_shape gv op` for `AnnAssign`, `Assign`, `AugAssign`, append/pop, and tuple/list replacement operations;
2. `assign_target_assignable_context cx gv st` for evaluated assignment targets;
3. AnnAssign non-`NoneT`/non-`NoneTV` obligations from `assignable_type`;
4. tuple/list assignment premises via `target_assignment_values_assignable`.

#### Approach
For scoped targets, use target typing plus env/runtime consistency and assignability preservation of target/expression evaluation. For top-level targets, use module-code/declaration/layout facts from runtime consistency and the static target typing relation; hashmap contexts must supply nonempty subscripts and slot success. For AnnAssign, use `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV`. For tuple/list assignment, package component facts into `target_assignment_values_assignable` rather than reopening assignment evaluation.

#### Not to try
Do not unfold `assign_target_def` in statement proofs. If top-level `assign_target_assignable_context` cannot be derived, escalate with the exact residual goal; this indicates a missing invariant or bridge lemma, not permission to weaken C3.

### C5.1: Shape side-condition lemmas
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: Shape matching is by finite operation/target-value cases and tuple length/list-relation facts.
- Dependencies: C3

#### Statement
Prove operation-specific lemmas concluding `assign_operation_matches_target_shape gv op` from the evaluated target/value facts available in statement assignment branches.

#### Approach
Base targets should close by the base-target shape lemma or direct simplification. Tuple replacement uses materialized RHS list length and component relation facts; append/pop/update cases use their operation-specific typing premises.

#### Not to try
Do not infer tuple length by ad hoc arithmetic after unfolding assignment; obtain it from the statement typing/materialization relation.

### C5.2: Assignable-context side-condition lemmas
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: This is exactly what `assign_target_assignable_context` names; scoped and top-level cases are finite and driven by target typing/runtime consistency.
- Dependencies: C3
- Checkpoint: yes

#### Statement
Prove lemmas concluding `assign_target_assignable_context cx gv st` for runtime values `gv` produced by well-typed assignment-target evaluation under `runtime_consistent env cx st`.

#### Approach
Scoped variables: use env consistency, scope lookup assignability, and evaluator assignability preservation facts. Top-level variables: use module code, declaration lookup, storage/hashmap layout-slot success, and nonempty hashmap subscript information from target path typing. Tuple targets: prove componentwise via `EVERY`.

#### Not to try
Do not replace this with weaker local assumptions in `eval_all_type_sound_mutual`.

### C5.3: AnnAssign assignable-type consequences
- Kind: `boundary_lemma`
- Risk: 1
- Rationale: The relevant lemmas already exist in `vyperTypeSystemScript.sml`; this component is mainly wiring them to statement hypotheses.
- Dependencies: C3

#### Statement
Prove any missing AnnAssign helper lemmas that derive non-`NoneT` and evaluated non-`NoneTV` facts from `assignable_type env.type_defs ty` and type evaluation hypotheses.

#### Approach
Use `assignable_type_not_NoneT`, `evaluate_type_not_NoneT_imp_not_NoneTV`, and `assignable_type_evaluate_not_NoneTV` directly. Keep these as small rewrite/drule helpers for statement branches.

#### Not to try
Do not add local `ty <> NoneT` assumptions to statement soundness.

### C5.4: Tuple/list assignment packaging
- Kind: `boundary_lemma`
- Risk: 2
- Rationale: The list relation was designed for `assign_targets`; proof is structural over target/value lists and materialization relations.
- Dependencies: C5.1, C5.2, C5.3

#### Statement
Prove lemmas packaging typed target lists, RHS/materialized values, and assignable contexts into `target_assignment_values_assignable env cx st tgts gvs vs` plus `EVERY (\gv. assign_target_assignable_context cx gv st) gvs`.

#### Approach
Induct over the aligned target/value lists or the existing list relation. The head case uses C5.1–C5.3; the tail case preserves the same environment/state premises until assignment execution begins.

#### Not to try
Do not prove this by repeated `EL`/`LENGTH` reasoning unless the source relation is already indexed; prefer `LIST_REL3` induction.

### C6: Assignment statement branches in `eval_all_type_sound_mutual`
- Kind: `mutual_theorem_cases`
- Risk: 2
- Rationale: After C5, these branches are integration: evaluate target/RHS, derive strengthened assignment premises, call C3/C4, and project the joint invariant.
- Required for completion: yes
- Dependencies: C1, C2, C3, C4, C5
- Checkpoint: yes

#### Statement
Remove the assignment-related cheats/scaffolding in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, especially `eval_all_type_sound_mutual[AnnAssign]`, `[Assign]`, `[AugAssign]`, tuple/list assignment, append/pop assignment, and any assignment-update branches identified by C0.

#### Approach
Follow evaluator order. Use expression/target soundness to type evaluated RHS and target values. At the assignment call, supply `assign_operation_runtime_typed`, `assign_operation_matches_target_shape`, and `assign_target_assignable_context` via C5, then invoke C3 or the C4 compatibility wrapper. `AugAssign` consumes C1/C2 for update-binop and leaf/subscript update soundness.

#### Not to try
Do not unfold `assign_target_def` or reprove top-level assignment branch logic in statement soundness.

### C7: Remaining statement evaluator mutual cases
- Kind: `mutual_theorem_cases`
- Risk: 2
- Rationale: These cases are branch-local consumers of existing fresh-stack infrastructure once assignment and builtin layers are complete. The architecture requires finishing them inside the existing joint invariant, not by separate no-TypeError trees.
- Required for completion: yes
- Dependencies: C1, C6
- Checkpoint: yes

#### Statement
Remove all remaining reachable cheats/suspended cases inside `eval_all_type_sound_mutual` not covered by C6, including current-source statement, statement-list, for-loop/iterator, target, expression, and expression-list branches found by C0.

#### Approach
For each evaluator branch, stay within the existing joint theorem and consume the layer-specific theorem: expression/target soundness for expression branches, scope-pop and env-extension/preservation for scoped blocks/loops, builtin soundness C1 for builtin expression branches, and assignment soundness C6 for assignment branches. If several cheated branches follow the same evaluator recursion, strengthen the existing mutual/frame invariant rather than starting a parallel theorem.

#### Not to try
Do not create standalone `*_no_type_error` inductions over the same evaluator. Do not prove call setup here if it belongs in C8.

### C8: Call and callable-body soundness wrappers
- Kind: `corollary_cluster`
- Risk: 2
- Rationale: The TASK lists four call wrappers; after statement soundness, these should be setup lemmas plus projections. Defaults/env extension/scope restoration helper theories already exist in the fresh stack.
- Required for completion: yes
- Dependencies: C7
- Checkpoint: yes

#### Statement
Remove reachable cheats in `semantics/prop/vyperTypeCallSoundnessScript.sml`, including `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, `special_call_no_type_error`, and any current-source callable-body wrapper required by `typed_callable_body_no_type_error`.

#### Approach
Prove narrow setup lemmas for call entry: argument/default value typing, environment extension, account/runtime consistency, signature lookup, and pushed-scope/pop restoration. Invoke completed statement/callable-body joint soundness and project no-TypeError or preservation conclusions for the wrappers.

#### Not to try
Do not build separate call no-TypeError and call preservation induction trees.

### C9: Public fresh surface and final zero-CHEAT build
- Kind: `final_verification`
- Risk: 1
- Rationale: After upstream reachable cheats are removed, this is a projection/build audit step. The TASK freezes only equivalent public behavior, not internal helper statements.
- Required for completion: yes
- Dependencies: C4, C7, C8
- Checkpoint: yes

#### Statement
Ensure `semantics/prop/vyperTypeSoundnessNewScript.sml` exposes wrappers equivalent in strength to the TASK-listed public surface:
- `typed_stmts_no_type_error`
- `typed_stmts_success_preserves_state_env`
- `typed_stmts_exception_preserves_state_and_return_type`
- `typed_expr_no_type_error`
- `typed_expr_success_preserves_type`
- `typed_callable_body_no_type_error`
Then `holbuild build vyperSemanticsHolTheory` must succeed with zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.

#### Approach
Keep `vyperTypeSoundnessNewScript.sml` as a projection layer. If names or internal theorem statements changed, provide compatibility corollaries of equivalent strength. Run the final build and a reachable-cheat audit; any remaining reachable cheat must map back to a previous component or trigger a plan augment.

#### Not to try
Do not weaken the frozen public behavior. Do not claim completion based on successful build if HOL reports reachable CHEAT warnings.
