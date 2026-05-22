# PLAN

## Structured Components

### C0: Build and CHEAT-audit the current fresh-stack baseline
- Kind: `source_audit`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: Mechanical holbuild/audit step; it records current source reality before proof edits and prevents work against stale handover notes.
- Checkpoint: yes
- Progress transition: `refinement`

#### Progress note
Preserves the previous baseline/audit component. It is not a proof obligation itself, but downstream components must use its current list of reachable CHEAT warnings as coverage evidence.

#### Summary
Run `holbuild build vyperTypeStatePreservationTheory` and `holbuild build vyperSemanticsHolTheory` or the closest permitted audit commands. Record every reachable `cheat`/unfinished `suspend` in the fresh stack. Use this only to refine exact work sites; do not expand scope to retired theories unless they are imported by `vyperSemanticsHolTheory`.

#### Description
The task’s source of truth is current SML source, with frozen public behavior only at the final wrapper surface. This component establishes the concrete remaining warnings and confirms whether the For_cons source already contains the helper-based patch or still has the old existential tail.

#### Statement
No theorem statement. Output is an audit list of reachable CHEAT/suspend warnings and first failing holbuild target, if any.

#### Approach
Use `holbuild`, not direct HOL. Prefer `vyperTypeStatePreservationTheory` first because the handover-focused assignment proof lives there, then `vyperSemanticsHolTheory` for full reachability. If current source differs from handover notes, treat source/audit as authoritative and close already-fixed leaves with evidence instead of re-editing.

#### Not to try
Do not start broad repository cleanup from grep output alone. Suspends in old retired theories or non-imported experiments are notes only unless the audit shows they are reachable from `vyperSemanticsHolTheory`.

### C1: Assignment-target state preservation and joint soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 10
- Work units: 0
- Rationale: The strengthened assignment interfaces already exist in source and the remaining work is split by evaluator branch. The hardest top-level storage cases are isolated to exact branch helpers rather than a new induction architecture.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1, TYPE_SYSTEM_REWRITE_PLAN assignment update 2026-05-13

#### Progress note
Carries forward the strengthened `assign_target_sound_mutual` architecture; no prior proof progress is invalidated. The old high-risk gate is replaced by branch-local low-risk leaves.

#### Summary
Finish the reachable assignment-target proofs in `vyperTypeStatePreservationScript.sml`. Do not weaken `assign_target_sound_mutual` or drop `assign_operation_matches_target_shape` / `assign_target_assignable_context`. Prove branch helpers that exactly match evaluator branches, then discharge compatibility wrappers in `vyperTypeAssignSoundnessScript.sml`.

#### Approach
Work branch-by-branch, closing each branch immediately after splitting on the evaluator result. Follow the proven `TopLevelVar` storage `Value` branch style from the handover: exact helper, narrow branch, then final no-TypeError/preservation theorem. Use C3 lemmas as theorem dependencies but do not re-prove the update-binop path inside this component.

#### Not to try
Do not weaken the strengthened side conditions to make callers easier. Do not use broad `gvs[..., AllCaseEqs()]` across the whole `TopLevelVar` proof and then try to repair dozens of goals; this was identified as unworkable.

#### Argument
The assignment proof is by the existing mutual recursion over `assign_target` and `assign_targets`. The invariant is joint/all-result where needed: state/accounts typing are preserved and TypeError is excluded under runtime target typing, runtime operation typing, shape matching, and assignable context. For top-level targets, `assign_target_assignable_context` supplies the static module/declaration/layout facts that prevent lookup/storage/hashmap shape errors from becoming TypeError; `target_runtime_typed` supplies the leaf type for recursive subscript assignment. Tuple/list targets consume the list IH and target/value assignability relation elementwise.

#### Definition design
Use the current definitions as proof interfaces, not rewrite targets. `assign_operation_matches_target_shape` prevents applying append/pop/update to the wrong target shape. `assign_target_assignable_context` is the runtime writability/context boundary: scoped assignability, top-level module existence, declaration shape, storage slot/hashmap slot availability, and nonempty hashmap subscript path. `target_assignment_values_assignable` is the tuple/list boundary and should supply both runtime typedness and assignability/context facts for each component. Failure sign: if a branch needs to inspect unrelated evaluator cases, add a small branch helper matching the semantic branch instead of broad `AllCaseEqs()` cleanup.

#### Code structure
Primary edits belong in `semantics/prop/vyperTypeStatePreservationScript.sml`, near existing storage/top-level helpers and the `Resume assign_target_sound_mutual[...]` blocks. Compatibility corollaries belong in `semantics/prop/vyperTypeAssignSoundnessScript.sml` only after the mutual theorem is cheat-free. Do not move static env-extension facts into this file; keep environment weakening in the existing env theories.

### C1.1: Finish preservation-only assignment branches
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These branches only require state/accounts preservation and are direct consumers of existing update/storage preservation lemmas.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.1

#### Progress note
Same obligation as prior preservation branch component, now authorized as a leaf.

#### Summary
Remove remaining preservation-only suspends/cheats for assignment target recursion if the C0 audit reports them reachable. Use `sound_ScopedVar` as the local model and mirror the evaluator recursion for top-level, immutable, tuple target, and target-list cons branches.

#### Statement
Current-source preservation mutual theorem(s) in `vyperTypeStatePreservationScript.sml` around the first assignment-target mutual proof, including suspended cases named `TopLevelVar`, `ImmutableVar`, `TupleTargetV`, and `assign_targets_cons` if still present.

#### Approach
Unfold only the relevant `assign_target`/`assign_targets` branch and use existing preservation lemmas for `set_var`, storage read/write, immutable operations, and recursive subscript assignment. For tuple/list targets, induct through the existing mutual IH rather than starting a new list induction outside the theorem.

#### Not to try
Do not prove a separate preservation theorem by re-inducting over targets. Do not touch no-TypeError branches here except where the source theorem combines them.

### C1.2: Prove `assign_target_sound_mutual[sound_TopLevelVar]` HashMapRef branch
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The handover identifies the exact branch and required facts; the proof should be a focused helper plus local branch discharge.
- Dependencies: C0
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2, TYPE_SYSTEM_REWRITE_PLAN lines 271-292

#### Progress note
Refines the old `TopLevelVar` high-risk case into the single HashMapRef branch with a branch-helper boundary.

#### Summary
Close the `lookup_global ... = INL (HashMapRef is_transient base_slot kt vt)` branch in `sound_TopLevelVar`. Add a narrowly stated helper if needed before editing the large `Resume` proof. The helper should bridge top-level hashmap declaration/context facts to recursive subscript no-TypeError/preservation after the hashmap prefix.

#### Statement
Inside `Theorem assign_target_sound_mutual`, `Resume assign_target_sound_mutual[sound_TopLevelVar]`: prove the `HashMapRef` semantic branch without `cheat`. Any helper must preserve the current theorem’s strengthened hypotheses, especially `assign_target_assignable_context cx gv st` and `assign_operation_matches_target_shape gv op`.

#### Approach
First isolate the branch by `lookup_global`. Use `assign_target_assignable_context` to obtain nonempty `sbs` and slot/declaration availability. Use `top_level_HashMap_decl` or equivalent lookup consistency to connect the returned `HashMapRef` with `HashMapT kt vt`, then use the strengthened `target_path_step_type` key invariant to traverse the hashmap prefix and call `assign_subscripts_no_type_error_runtime_typed` on the value-type suffix.

#### Not to try
Do not attempt the branch inside a large unexplained `AllCaseEqs()` split. Do not treat hashmap key evaluation as an untyped runtime fact; the strengthened `target_path_step_type` is the intended source of key well-typedness.

### C1.3: Prove `assign_target_sound_mutual[sound_TopLevelVar]` ArrayRef branch
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: ArrayRef is localized to storage-array assignment operations and can be split into append/pop versus ordinary element/path update.
- Dependencies: C0
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2, TYPE_SYSTEM_REWRITE_PLAN lines 293-300

#### Progress note
Splits the previous combined top-level residual into the ArrayRef branch after HashMapRef.

#### Summary
Close the `ArrayRef` top-level branch in `sound_TopLevelVar`. Handle storage-array `AppendOp`/`PopOp` separately from ordinary subscript assignment. Reuse existing array traversal and storage write/read no-TypeError helpers rather than unfolding storage internals in the mutual proof.

#### Statement
Inside `Theorem assign_target_sound_mutual`, `Resume assign_target_sound_mutual[sound_TopLevelVar]`: prove the `ArrayRef` semantic branch without `cheat`.

#### Approach
Split on the assignment operation before destructing storage details. For append/pop use `assign_operation_runtime_typed` shape facts to get dynamic-array requirements. For ordinary element/path assignment, resolve the array element/reference, establish the recursive leaf type, invoke `assign_subscripts_no_type_error_runtime_typed`, and finish with the storage write no-TypeError/value typing helper.

#### Not to try
Do not conflate `ArrayRef` with the already-proved storage `Value` branch; array references have distinct append/pop and element-resolution paths. Do not bypass operation-shape side conditions.

### C1.4: Finish `sound_ImmutableVar` and `sound_TupleTargetV` branches
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: Both branches are structurally simpler than top-level storage: immutable assignment is ruled out by assignability/context, and tuple targets follow the existing target-list relation.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2

#### Progress note
Keeps the two named TASK residuals together because they are small non-storage branches of the same mutual theorem.

#### Summary
Remove cheats from `sound_ImmutableVar` and `sound_TupleTargetV` in `assign_target_sound_mutual`. Immutable writes should be impossible or no-TypeError by context; tuple target assignment should delegate to the target-list mutual conjunct.

#### Statement
`Resume assign_target_sound_mutual[sound_ImmutableVar]` and `Resume assign_target_sound_mutual[sound_TupleTargetV]` in current source.

#### Approach
For `ImmutableVar`, unfold the assignment target evaluator enough to expose the impossible writable assignment/context contradiction or the non-TypeError lookup path. For `TupleTargetV`, use the mutual theorem’s target-list conjunct and `target_assignment_values_assignable` to supply per-element value typing and assignability.

#### Not to try
Do not introduce a special-purpose tuple assignment induction outside the mutual theorem. Do not weaken immutable assignability assumptions; immutable writes must be ruled out by the existing context predicate.

### C1.5: Finish `sound_assign_targets_cons` target-list branch
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: The cons case follows the recursive structure of `assign_targets`; the IHs correspond to head target and tail target-list assignments.
- Dependencies: C0, C1.4
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.2

#### Progress note
Covers the TASK-named `sound_assign_targets_cons` residual.

#### Summary
Remove the cheat from the cons case of the assignment target-list soundness conjunct. Split on head assignment result, then tail assignment result, preserving all-result state/account invariants and excluding TypeError in each branch.

#### Statement
`Resume assign_target_sound_mutual[sound_assign_targets_cons]` in current source.

#### Approach
Use the head-target IH under the head value/type/assignability facts, then use the tail-list IH on the post-head state. The context predicate for target lists should be consumed elementwise; if missing in the local context, prove a small projection lemma for `target_assignment_values_assignable` rather than destructing the full typing relation repeatedly.

#### Not to try
Do not assume the state is unchanged after the head assignment. Assignment soundness is all-result precisely because partial updates may occur before later failure.

### C1.6: Refresh assignment compatibility wrappers
- Kind: `proof`
- Risk: 1
- Work priority: 50
- Work units: 3
- Rationale: Once the mutual theorem has no local cheats, these wrapper theorems are direct projections/corollaries.
- Dependencies: C1.2, C1.3, C1.4, C1.5
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C1.3

#### Progress note
Same wrapper obligation as before; no architecture change.

#### Summary
Prove or repair `assign_target_no_type_error`, `assign_target_update_no_type_error`, and `assign_target_append_no_type_error` in `vyperTypeAssignSoundnessScript.sml` as compatibility corollaries. They should not drive internal proof structure.

#### Statement
Current-source theorems in `semantics/prop/vyperTypeAssignSoundnessScript.sml`: `assign_target_no_type_error`, `assign_target_update_no_type_error`, `assign_target_append_no_type_error`.

#### Approach
Import/use the appropriate conjunct of `assign_target_sound_mutual`; instantiate operation and side conditions, then project `no_type_error_eval` or result no-TypeError. If a wrapper lacks a hypothesis now required by the strengthened theorem, either derive it from existing wrapper premises or make it a compatibility theorem for the corrected stronger internal theorem, updating only callers permitted by the task.

#### Not to try
Do not duplicate target evaluator case analysis in these wrappers. Do not keep old weaker wrappers with cheats if their callers actually need the stronger side conditions.

### C2: Carry-forward ancestor context for statement soundness work
- Kind: `ancestor_context`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Included only to satisfy dotted-component parent validation. This augment does not re-plan C2 or its siblings; the actual risk-bearing work is inside C2.1.1.13.4.3.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2 plan

#### Progress note
Carry-forward parent context only; no executable work or scope expansion is introduced by this component in this update.

#### Summary
Parent context only for the local C2.1.1.13.4.3 repair. No siblings or broader statement-soundness obligations are changed by this update.

#### Description
This component is emitted solely because the structured PLAN validator requires explicit dotted parents. The executable frontier introduced by this update is under C2.1.1.13.4.3.

#### Argument
The global statement-soundness argument is unchanged. The local repair below stabilizes one subscript-expression adapter proof and does not alter the broader invariant.

#### Definition design
No definition-design change at this ancestor level. Local proof interfaces are described at C2.1.1.13.4.3.

#### Code structure
No ancestor-level file organization changes. All actual edits authorized by this update are in `semantics/prop/vyperTypeStmtSoundnessScript.sml` under the local subscript proof region.

### C2.0: Carry forward completed TopLevelName and assignment-statement repairs
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Accepted checkpoint evidence already proves and builds the old C2 gate obligations; this component is only bookkeeping so the replacement subtree does not lose prior progress.
- Supersedes: C2.1, C2.1.0, C2.1a, C2.1a.1, C2.1a.2, C2.1a.3, C2.1a.3.1, C2.1a.3.2, C2.1a.3.3, C2.1a.4, C2.1a.5, C2.1a.6, C2.1a.7, C2.1a.7.1, C2.1a.7.2, C2.1a.7.3, C2.1a.8, C2.1a.9, C2.1b, C2.2, C2.3, C2.4
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0592, E0593, E0594, E0597, E0598, E0599, E0600, E0601, E0602, E0603, E0604, E0609, E0610, E0611, E0612, E0613, E0614, E0615

#### Progress note
No new source edits. This leaf records that all old C2 TopLevelName/assignment descendants are accepted done and should not block the remaining expression-resume schedule.

#### Summary
- No executor edits required.
- Treat old C2 TopLevelName repair and assignment statement repairs as done.
- Baseline evidence: `vyperTypeStmtSoundnessTheory` builds after those repairs.
- Next work starts at remaining expression resumes, not old C2.1a probes.

#### Statement
No theorem statement; carried checkpoint/build evidence only.

#### Approach
Begin this component only if the harness requires an executable carry-forward leaf; otherwise it is just dependency bookkeeping. Do not touch source.

#### Not to try
Do not retry old C2.1a layout/scanner probes or tuple/list assignment audits.

### C2.1: Carry-forward ancestor context for expression/statement mutual proof
- Kind: `ancestor_context`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Included only to provide explicit parentage for C2.1.1.13.4.3. The local subtree replacement lowers the administrative blocker without changing this ancestor's obligations.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.1 plan

#### Progress note
No new work at this level; the child subtree contains the full executable repair.

#### Summary
Carry-forward parent context only. The local work below concerns `Expr_Subscript` support lemmas and a preceding `BaseTarget_Subscript` performance refactor.

#### Description
This component is not an authorization to edit outside C2.1.1.13.4.3. It exists only to satisfy explicit parent requirements in the structured PLAN output.

#### Argument
The mutual evaluator proof strategy is unchanged: prove the strongest joint invariant once along evaluator recursion and use local boundary lemmas to avoid duplicated case analysis.

#### Definition design
No new definitions at this ancestor. The relevant interfaces remain the mutual IHs and local subscript helper lemmas.

#### Code structure
No changes outside the local `vyperTypeStmtSoundnessScript.sml` proof blocks named in the child components.

### C2.1.0: Carry forward completed Targets_cons timeout refactor
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: The Targets_cons refactor was already proved and built. It is retained only as dependency/progress bookkeeping under the rebased C2.1 subtree.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.0, E0617

#### Summary
- No source work.
- Retains the completed `Targets_cons` proof-refactor evidence.
- Exists so the rebased subtree does not lose prior proof progress.
- Downstream work may assume the old timeout-prone proof has already been repaired.

#### Statement
No new theorem statement. Existing `Resume eval_all_type_sound_mutual[Targets_cons]` remains proved in source.

#### Approach
If forced to act on this component, audit that `vyperTypeStmtSoundnessTheory` has already built past `Targets_cons`; otherwise do nothing.

#### Not to try
Do not edit the old Targets_cons proof while working on Expr_Subscript.

### C2.1.1: Carry-forward ancestor context for eval_all_type_sound_mutual
- Kind: `ancestor_context`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: This parent is carried forward so the dotted local component is well-formed in the PLAN. It does not add or revise sibling obligations.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.1.1 plan

#### Progress note
Ancestor context only; no proof work at this level in this update.

#### Summary
Carry-forward context for the local subscript-expression repair. All executable edits remain below C2.1.1.13.4.3.

#### Description
The current update responds to an administrative stuck episode in a local subscript adapter. It does not redesign the whole mutual theorem.

#### Argument
The local adapter contributes to the `Expr_Subscript` branch of the mutual theorem by reusing the projection helper rather than duplicating evaluator case analysis.

#### Definition design
No ancestor-level definition changes. The local proof relies on existing `well_typed_expr`, `type_place_expr`, and result-typing relations.

#### Code structure
Authorized edits are local to the `BaseTarget_Subscript` resume and the `expr_subscript_place_as_ordinary_branch_sound_stmt` theorem.

### C2.1.1.0: Carry forward completed structural-expression and statement-branch repairs
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already closed evidence supports this placeholder; no proof work remains.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.1.0, E0655

#### Summary
- No executor edits.
- Carries prior completed structural-expression/statement branch repairs.
- Maintains progress continuity after rebasing C2.1.
- Does not schedule any new proof work.

#### Statement
No new theorem statement.

#### Approach
Treat as done bookkeeping. Do not begin unless the harness requires no-op evidence.

#### Not to try
Do not reopen old structural branch repairs while the current frontier is Expr_Subscript.

### C2.1.1.10: Carry forward completed Expr_FlagMember proof-order repair
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 10
- Work units: 0
- Rationale: The FlagMember Resume repair was already proved and is retained as completed evidence.
- Dependencies: C2.1.1.9
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.1.10, E0660

#### Summary
- No executor work.
- Carries completed `Expr_FlagMember` repair.
- Retains prior progress after the subtree rebase.
- Current editing remains confined to `Expr_Subscript`.

#### Statement
No new theorem statement; existing branch remains proved.

#### Approach
No action unless a build regression points here.

#### Not to try
Do not use FlagMember as a reason to broaden the active Subscript component.

### C2.1.1.11: Carry forward completed Expr_IfExp ordinary/place split repair
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 11
- Work units: 0
- Rationale: The IfExp repair was accepted and built through; it remains useful as pattern evidence but no work remains.
- Dependencies: C2.1.1.10
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.1.11, E0663

#### Summary
- No executor work.
- Carries completed `Expr_IfExp` split-first repair.
- Provides pattern evidence for Subscript ordinary/place conclusion handling.
- Do not copy its place-`NONE` contradiction to Subscript.

#### Statement
No new theorem statement; existing branch remains proved.

#### Approach
Use as conceptual precedent only: split the joint conclusion before consuming typing. Do not edit this branch.

#### Not to try
Do not apply the IfExp place-vacuity argument to Subscript; Subscript has a real place projection.

### C2.1.1.12: Carry forward completed Expr_StructLit split repair
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 12
- Work units: 0
- Rationale: The StructLit repair was accepted and holbuild advanced past it to Subscript. It is retained as completed evidence and immediate predecessor of the current frontier.
- Dependencies: C2.1.1.11
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.1.12, E0664

#### Summary
- No executor work.
- Carries accepted StructLit closure evidence.
- Confirms holbuild now exposes `Expr_Subscript` as the current branch.
- The next source edit belongs only to `C2.1.1.13`.

#### Statement
No new theorem statement; existing branch remains proved.

#### Approach
No action. Its successful split-first structure is precedent, but its vacuous place projection should not be reused for Subscript.

#### Not to try
Do not reopen StructLit unless holbuild regresses before Subscript.

### C2.1.1.13: Carry-forward ancestor context for expression cases
- Kind: `ancestor_context`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Included only as an explicit parent for C2.1.1.13.4.3. The broader expression-case plan is not changed.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.1.1.13 plan

#### Progress note
No sibling expression cases are touched by this update.

#### Summary
Carry-forward parent context for the subscript-expression proof repair. No broader expression-case obligations are re-planned here.

#### Description
The local stuck episode arose before holbuild could verify a subscript adapter. This parent context records that the repair remains within the expression-subscript branch.

#### Argument
Expression soundness follows evaluator recursion. For subscript expressions, local helper lemmas separate ordinary static typing, place-as-ordinary static typing, and projection behavior.

#### Definition design
No new definitions. Existing subscript helper lemmas are the intended boundary interface.

#### Code structure
No file movement. Edits remain in `vyperTypeStmtSoundnessScript.sml`.

### C2.1.1.13.1: Normalize the partial Expr_Subscript proof area
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This cleanup was already completed and reviewed in E0678; replacement carries it forward so downstream dependencies remain explicit without redoing work.
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0678, commit 21f9cd3ea

#### Progress note
The previous normalized placeholder and removal of the bad shared tail are preserved. No executor work is intended for this carried-forward leaf.

#### Summary
- Carried-forward completed cleanup.
- The shared brittle Expr_Subscript tail was removed.
- The current source has a simple placeholder Resume that later leaves will fill.
- This leaf remains as an explicit dependency for the helper and Resume proof leaves.

#### Description
No new edits are planned here. The purpose of retaining this leaf in the replacement subtree is to preserve the proof-history dependency and prevent downstream work from assuming the old shared-tail proof structure.

#### Approach
Treat E0678 as the closure evidence. If the harness unexpectedly offers this leaf as beginable, query/review rather than editing; the source cleanup should already be present.

#### Not to try
Do not resurrect any of the removed shared-tail tactic code. Do not perform additional formatting or broad cleanup in this leaf.

### C2.1.1.13.2: Make cold build pass and prove the Subscript place-projection tail helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: This is a localized proof-performance refactor plus a local boundary lemma following the already-proved `expr_subscript_place_tail_sound_stmt` structure. It has no definition changes and no cross-theory semantic uncertainty.
- Dependencies: C2.1.1.13.1
- Checkpoint: yes
- Supersedes: C2.1.1.13.2.1, C2.1.1.13.2.2
- Progress transition: `refinement`
- Carries progress/evidence from: pending source insertion of expr_subscript_place_projection_tail_sound_stmt with cheat, TO_type_system_rewrite-20260522T073012Z_m38723_t001
- Invalidates prior progress/evidence: separate tactical-child split under C2.1.1.13.2

#### Progress note
The prior two-child split is collapsed. The same episode may edit the earlier IfExp proof enough for cold `holbuild` to reach this area, then prove the projection-tail helper. This is one beginable leaf because the IfExp edit is only a strict build prerequisite, not a separate durable obligation.

#### Summary
- First remove the cold-build timeout in `ifexp_branch_from_cond_ih` by replacing the initial broad `rw[]` with controlled proof setup.
- Then prove `expr_subscript_place_projection_tail_sound_stmt` where it is already inserted with a temporary cheat.
- The helper conclusion must be `place_expr_result_typed env tv result_vt` for successful results.
- Prove by adapting `expr_subscript_place_tail_sound_stmt`, splitting on `base_vt` and keeping evaluator-tail unfolding local.
- Verify with `holbuild build vyperTypeStmtSoundnessTheory` and checkpoint the result.

#### Description
This leaf is the active repair gate. The source currently contains the intended helper statement with a cheat, but cold build fails earlier at `ifexp_branch_from_cond_ih`. The executor is authorized to make the minimal local IfExp proof refactor needed for holbuild, then replace the helper cheat with a proof. No mutual Resume work belongs in this leaf.

#### Statement
Expected local theorem shape:

```sml
Theorem expr_subscript_place_projection_tail_sound_stmt[local]:
  !cx env e e' v9 base_vt result_vt base_tv idx_tv idx st res st'.
    state_well_typed st /\
    env_consistent env cx st /\
    accounts_well_typed st.accounts /\
    well_formed_type env.type_defs v9 /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME result_vt /\
    vtype_annotation_ok result_vt v9 /\
    place_expr_result_typed env base_tv base_vt /\
    expr_result_typed env e' idx_tv /\
    get_Value idx_tv st = (INL idx,st) /\
    (do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                   "Subscript array type";
       check_array_bounds cx base_tv idx;
       res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv base_tv idx);
       case res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => place_expr_result_typed env tv result_vt | INR _ => T)
```

Do not change this statement unless the current source has already type-corrected it with equivalent binder names or harmless formatting differences.

#### Approach
For `ifexp_branch_from_cond_ih`, avoid the timeout-causing `rw[]`; introduce assumptions with `rpt gen_tac`, `strip_tac`/targeted simplification only as needed, then reuse the existing `first_x_assum ...`, case split on `res`, and `expr_result_typed_IfExp_branch` tail. For the Subscript helper, copy the structure of `expr_subscript_place_tail_sound_stmt`: derive `env.type_defs = get_tenv cx`, split on `base_vt`, use `vtype_annotation_ok_def`, `place_expr_result_typed_def`, `subscript_vtype_def`, and unfold the monadic tail only after fixing the branch. In the Type/Array branch, use `evaluate_subscript_typed_stmt`, `evaluate_subscript_success_not_HashMapRef_stmt`, `evaluate_subscript_error_not_TypeError_stmt`, and `check_array_bounds_error_not_TypeError_stmt` as in the existing helper, but finish successful values with `place_expr_result_typed_def`. In the HashMap branch, simplify through `check_array_bounds_hashmap_stmt` and `evaluate_subscript_def`, then use `read_storage_slot_state`, `read_storage_slot_success_type`, and `read_storage_slot_error`; the successful returned `Value` should satisfy `place_expr_result_typed` for `result_vt` after the `subscript_vtype`/annotation simplification.

#### Not to try
Do not prove this by unfolding the future `Expr_Subscript` Resume context; stay inside the local helper. Do not use quoted ASSUME/MATCH_MP plumbing for the monadic tail—if that seems necessary, the branch has not been simplified locally enough. Do not weaken the helper to return `expr_result_typed`; that fails for nested place/hashmap projections and will not support C2.1.1.13.4. Do not start C2.1.1.13.3 or C2.1.1.13.4 until this leaf builds cold.

### C2.1.1.13.3: Ordinary Expr_Subscript via an ordinary-base tail boundary helper
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The theorem is not suspect; existing place-tail helpers and lower-level subscript lemmas already prove the hard runtime cases. The risk mismatch came from an inline proof shape. With a helper matching the live monadic tail, the remaining Resume wiring should be standard IH application and result-case splitting.
- Checkpoint: yes
- Supersedes: E0681
- Progress transition: `refinement`
- Carries progress/evidence from: C2.1.1.13.2, TO_type_system_rewrite-20260522T073012Z_m38851_t001, TO_type_system_rewrite-20260522T073012Z_m38853_t001, TO_type_system_rewrite-20260522T073012Z_m38855_t001, TO_type_system_rewrite-20260522T073012Z_m38857_t001

#### Progress note
Prior episode E0681 is accepted as a blocking/stuck result for the old inline leaf. The mathematical obligation is unchanged, but the proof interface is refined: prove an ordinary-base tail helper before rewriting the Resume body. Existing place-tail helper progress remains useful.

#### Summary
- Replace the failed inline ordinary Expr_Subscript proof by a helper-driven proof.
- Add a local ordinary-base subscript tail lemma matching the evaluator monadic tail after base and index have both succeeded.
- Then the Resume ordinary conjunct only applies base/index IHs, handles error propagation, and invokes the helper for the success tail.
- This is a local proof-interface repair; no source theorem statement or broader architecture changes are intended.

#### Description
This subtree closes the ordinary expression half of `Resume eval_all_type_sound_mutual[Expr_Subscript]`. The failed episode showed that manipulating the large `case (base_res,st1)` evaluator tail inline leads to brittle assumption selection and unhelpful case splits. The replacement strategy is to prove one durable boundary lemma for the successful ordinary-base/index tail, analogous in spirit to `expr_subscript_place_tail_sound_stmt` but returning `expr_result_typed` for the ordinary Subscript expression.

#### Approach
Prove the helper first, then use it from the Resume. In the Resume, unfold `well_typed_expr_def` once, split the ordinary/static alternatives explicitly, apply the base IH immediately and bind/project its ordinary result, split the actual `eval_expr cx e st` equation before losing the pair variables, then apply the index IH only in the base-success branch. Error branches should be solved by the propagated no-TypeError/invariant facts from the relevant IH and simple evaluator simplification.

#### Not to try
Do not continue the old inline proof that unfolds and reasons through the whole subscript tail inside the Resume; E0681 shows this produces brittle assumption-selection and case-splitting failures. Do not select the base IH with exact `qpat_x_assum` patterns over the full conclusion. Do not use broad `gvs[]` immediately after the large evaluator split; it timed out. Do not case-split on a renamed `base_res` after it is no longer syntactically free.

#### Argument
For an ordinary typed `Subscript v9 e e'`, `well_typed_expr_def` gives `well_typed_expr env e`, `well_typed_expr env e'`, `well_formed_type env.type_defs v9`, and `subscript_type_ok (expr_type e) (expr_type e') v9`. The mutual IH for `e` gives state/env/accounts preservation, no TypeError, and, on success, `expr_result_typed env e base_tv`; error results propagate directly. On base success, the mutual IH for `e'` at the intermediate state gives the same facts for the index expression; index evaluation errors also propagate directly. If `get_Value` on the index fails, `expr_result_typed env e' idx_tv` plus the definition of `get_Value` should show the propagated error is not a TypeError. If `get_Value` succeeds, the remaining evaluator tail is exactly the ordinary subscript runtime: lift the array type, check bounds, evaluate the subscript, and possibly read storage. That tail is proved once in a helper using `evaluate_subscript_typed_stmt`, `evaluate_subscript_error_not_TypeError_stmt`, `check_array_bounds_error_not_TypeError_stmt`, and `expr_subscript_storage_tail_sound_stmt`.

#### Definition design
Do not introduce new semantic definitions. The proof interface is a local theorem whose assumptions are the facts naturally available after the base and index IHs: invariants at the post-index state, `expr_result_typed` for the base and index results, successful `get_Value`, `subscript_type_ok`, well-formed result annotation, and the exact monadic tail equality. The helper conclusion must match the ordinary Resume success-tail goal directly: state/env/accounts preservation, `no_type_error_result res`, and success `expr_result_typed env (Subscript v9 e e') tv`. Failure signs: if the Resume proof still needs to unfold `evaluate_subscript_def` or `check_array_bounds_def` directly, the helper statement is too weak; if it requires exact `qpat_x_assum` over the mutual IH conclusion, the IH should be projected immediately instead of selected later.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near the existing local Subscript lemmas (around lines 6543-6980) and the `Resume eval_all_type_sound_mutual[Expr_Subscript]` body. Place the new ordinary-tail helper after `expr_subscript_place_projection_tail_sound_stmt` and before the Resume. Keep it `[local]`. Do not move existing helper definitions or alter public theorem names. The old exploratory `FAIL_TAC` prefix in the Resume must be removed as part of the final proof rewrite.

### C2.1.1.13.3.1: Stabilize the Expr_Subscript Resume editing point
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: The working source contains exploratory failing edits ending in `FAIL_TAC`; removing or overwriting them is mechanical and prevents proof-search artifacts from contaminating the helper-driven rewrite.
- Progress transition: `refinement`
- Carries progress/evidence from: E0681

#### Progress note
Carries forward the stuck evidence only as guidance about what to remove; no proved theorem progress is claimed for the exploratory prefix.

#### Summary
Remove the failed exploratory ordinary-Subscript prefix and start the Resume rewrite from a clean placeholder. Preserve all already-proved local helpers above the Resume. The build may still fail at remaining cheats/placeholders, but it should not fail because of an intentional `FAIL_TAC`.

#### Description
Inspect `git diff -- semantics/prop/vyperTypeStmtSoundnessScript.sml`. Either restore the simple placeholder from commit `bdbd420` or overwrite the body while implementing later components. The important invariant is that no obsolete `qpat_x_assum`/`FAIL_TAC` probe remains in the final source.

#### Statement
No HOL theorem statement; source cleanup for `Resume eval_all_type_sound_mutual[Expr_Subscript]`.

#### Approach
Keep the proven helper block ending at `expr_subscript_place_projection_tail_sound_stmt`. Remove only exploratory code in the Resume body around lines 6987-7004. If doing this together with later proof edits, ensure `holbuild` failures point to genuine remaining proof obligations, not the old intentional failure.

#### Not to try
Do not stage unrelated untracked probe files. Do not delete the existing place-tail helpers or lower-level subscript lemmas.

### C2.1.1.13.3.2: Prove ordinary-base Subscript successful-tail helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: This is a direct analogue/composition of already-proved local helper lemmas. It packages the runtime tail that E0681 showed should not be unfolded in the mutual Resume body.
- Dependencies: C2.1.1.13.3.1
- Checkpoint: yes
- Carries progress/evidence from: C2.1.1.13.2

#### Progress note
Uses existing local lemmas proved before the failed Resume work, especially `evaluate_subscript_typed_stmt`, `evaluate_subscript_error_not_TypeError_stmt`, `check_array_bounds_error_not_TypeError_stmt`, and `expr_subscript_storage_tail_sound_stmt`.

#### Summary
Add a `[local]` theorem for the ordinary-base/index-success subscript evaluator tail. Inputs are invariants, ordinary `expr_result_typed` facts for base and index, successful `get_Value`, static `subscript_type_ok`, well-formed annotation, and the exact tail equality. Output is preservation, no TypeError, and ordinary `expr_result_typed` for `Subscript` on success.

#### Description
This helper should cover only the tail after `eval_expr cx e st` has produced `INL base_tv`, `eval_expr cx e' st1` has produced `INL idx_tv`, and `get_Value idx_tv st2 = (INL idx, st2)`. It should not mention the mutual IHs or evaluate either subexpression. Its purpose is to make the Resume success branch an `irule`/`drule_all` call rather than another evaluator-tail proof.

#### Statement
Suggested statement shape (adjust variable names/types to compile, but keep this interface):

```sml
Theorem expr_subscript_ordinary_tail_sound_stmt[local]:
  !cx env e e' v9 base_tv idx_tv idx st res st'.
    state_well_typed st /\
    env_consistent env cx st /\
    accounts_well_typed st.accounts /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    expr_result_typed env e base_tv /\
    expr_result_typed env e' idx_tv /\
    get_Value idx_tv st = (INL idx,st) /\
    (do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                   "Subscript array type";
       check_array_bounds cx base_tv idx;
       sub_res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv base_tv idx);
       case sub_res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR _ => T)
```

#### Approach
Start by deriving `env.type_defs = get_tenv cx` from `env_consistent`. Open `expr_result_typed_def`/`expr_runtime_typed_def` for the base and index facts only enough to obtain `evaluate_type (get_tenv cx) (expr_type e) = SOME arr_tv`, `toplevel_value_typed base_tv arr_tv`, `~is_HashMapRef base_tv`, and from `get_Value` an index runtime value typed at `expr_type e'`. Then unfold the monadic tail: array-type lift failure should contradict the base typing; `check_array_bounds` error uses `check_array_bounds_error_not_TypeError_stmt`; `evaluate_subscript` success uses `evaluate_subscript_typed_stmt` plus `expr_subscript_storage_tail_sound_stmt` for storage references; `evaluate_subscript` error uses `evaluate_subscript_error_not_TypeError_stmt`.

#### Not to try
Do not include `eval_expr` assumptions or mutual IH assumptions in this helper; that would recreate the brittle Resume proof. Do not split static place-expression alternatives here; this helper is only the ordinary `subscript_type_ok` path. Do not unfold `read_storage_slot` internals; use `expr_subscript_storage_tail_sound_stmt`, `read_storage_slot_state`, `read_storage_slot_success_type`, and `read_storage_slot_error` through the existing helper where possible.

### C2.1.1.13.3.3: Rewrite the ordinary Expr_Subscript conjunct using IHs and the tail helper
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: After the helper, the Resume body is routine evaluator sequencing: base IH, error propagation, index IH, get_Value split, helper invocation. The main source of prior risk—inline tail reasoning—is removed.
- Dependencies: C2.1.1.13.3.2
- Checkpoint: yes
- Supersedes: E0681
- Progress transition: `refinement`
- Carries progress/evidence from: TO_type_system_rewrite-20260522T073012Z_m38851_t001

#### Progress note
Refines the failed ordinary-half proof by reusing the same initial unfolding insight but replacing brittle assumption selection and tail case analysis with the new helper.

#### Summary
Complete the first conjunct of `Resume eval_all_type_sound_mutual[Expr_Subscript]`. Split the ordinary/static Subscript typing branch, apply base and index IHs immediately, solve propagated-error branches from IH facts, and invoke `expr_subscript_ordinary_tail_sound_stmt` for the base/index/get_Value success tail. Leave the second/place conjunct to the existing sibling/next component unless already in scope of the current Resume proof skeleton.

#### Description
The ordinary conjunct proves: under `well_typed_expr env (Subscript v9 e e')`, evaluation of the Subscript preserves state/env/accounts, has no TypeError, and returns an `expr_result_typed` value on success. The proof should not try to prove place-result typing; that belongs to the second conjunct/place half. However, because the theorem Resume contains both conjuncts, keep the existing placeholder/cheat for the second conjunct if this component is explicitly only the ordinary half.

#### Statement
Inside:

```sml
Resume eval_all_type_sound_mutual[Expr_Subscript]:
  ...
QED
```

complete the first `conj_tac` branch corresponding to the ordinary expression half:

```sml
well_typed_expr env (Subscript v9 e e') ==>
state_well_typed st' /\ env_consistent env cx st' /\
accounts_well_typed st'.accounts /\ no_type_error_result res /\
(case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR _ => T)
```

#### Approach
After unfolding `well_typed_expr_def` once, handle only the ordinary static disjunct (`well_typed_expr env e`, `well_typed_expr env e'`, `well_formed_type env.type_defs v9`, `subscript_type_ok ...`). Apply the base IH to the exact `eval_expr cx e st = (base_res,st1)` before destructing facts; immediately derive and name the ordinary base conclusion by applying it to `well_typed_expr env e`. Split `base_res`: the error branch is evaluator propagation plus the base IH no-TypeError/invariants; the success branch applies the index IH at `st1`, derives the ordinary index conclusion with `well_typed_expr env e'`, splits index result and `get_Value`, and calls `expr_subscript_ordinary_tail_sound_stmt` in the all-success branch.

#### Not to try
Do not use exact `qpat_x_assum` over `well_typed_expr env e ==> ...`; apply the IH continuation immediately and keep the resulting conjunction as a named/top-stack fact. Do not use `simp[]` on the whole implication/tail goal; use targeted `simp_tac` with `Once evaluate_def`, `bind_def`, `return_def`, `raise_def`, and case-specific facts. Do not split `FST (eval_expr cx e st)` unless the direct pair split on `eval_expr cx e st` is unavailable; preserve the equation so substitutions are useful.

### C2.1.1.13.4: Carry-forward ancestor context for Expr_Subscript local helpers
- Kind: `ancestor_context`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The child repair removes an administrative blocker in one local helper path. This parent remains standard risk because all uncertainty is decomposed into low-risk/refined children below.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.1.1.13.4 plan

#### Progress note
Parent context only. The replacement of C2.1.1.13.4.3 does not re-plan siblings such as ordinary-static or other subscript branches.

#### Summary
Carry-forward context for the `Expr_Subscript` helper group. The only changed path is the place-as-ordinary adapter and its local prefix-build prerequisite.

#### Description
The proof architecture for `Expr_Subscript` remains: split static alternatives at the boundary and discharge each with a local adapter/helper. The update below handles the place-as-ordinary adapter path only.

#### Argument
The `Expr_Subscript` case is proved by splitting the static typing derivation. The place-as-ordinary branch evaluates the base, uses the place-expression IH to obtain runtime place typing, delegates successful projection to the projection helper, and converts the resulting place typing to expression typing.

#### Definition design
No new definitions. The relevant proof interface consists of `expr_subscript_place_projection_branch_sound_stmt`, `place_expr_result_typed_expr_result_typed_stmt`, and the expression/place halves of the mutual IH.

#### Code structure
Keep all helper proofs local in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near the existing `Expr_Subscript` proof. Do not move this local adapter into another theory.

### C2.1.1.13.4.1: Replace the broken broad helper with two adapter skeletons
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: This is mechanical source stabilization after E0695: remove the intentionally partial failing proof shape and install precise local theorem statements. Temporary `cheat` skeletons are acceptable only in this leaf so later leaves can replace them one at a time.
- Carries progress/evidence from: E0695
- Invalidates prior progress/evidence: partial expr_subscript_ordinary_branch_sound_stmt source from E0695

#### Progress note
Uses E0695 as evidence that the broad helper should be deleted/replaced, not repaired tactically.

#### Summary
Delete or overwrite the current partial `expr_subscript_ordinary_branch_sound_stmt`. Add two local theorem skeletons with the exact statements described below. Rewrite the ordinary conjunct of `Resume eval_all_type_sound_mutual[Expr_Subscript]` to split the static `well_typed_expr` fact and call these skeletons. Verify `vyperTypeStmtSoundnessTheory` builds through this area, allowing only the new temporary skeleton cheats.

#### Description
This leaf is a cleanup/refactor gate, not a final proof. It should leave no `FAIL_TAC` probe and no half-proved broad helper. If temporary cheats are introduced, they must be exactly the two adapter skeletons named here and must be eliminated by C2.1.1.13.4.2 and C2.1.1.13.4.3.

#### Statement
Skeleton 1:
```sml
Theorem expr_subscript_ordinary_static_branch_sound_stmt[local]:
  !cx env e e' v9 st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e /\ well_typed_expr env e' /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    <base-expression mutual IH for e> /\
    <index-expression mutual IH for e'> ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
```

Skeleton 2:
```sml
Theorem expr_subscript_place_as_ordinary_branch_sound_stmt[local]:
  !cx env e e' v9 base_vt st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e' /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME (Type v9) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    <base-expression mutual IH for e> /\
    <index-expression mutual IH for e'> ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
```
Use the exact IH quantifier blocks already present in `expr_subscript_ordinary_branch_sound_stmt`.

#### Approach
Make the statements syntactically match the existing mutual IH blocks so callers can `irule` them without manual theorem construction. In the Resume ordinary conjunct, `mp_tac` the `well_typed_expr env (Subscript ...)` assumption, simplify with `Once well_typed_expr_def` and `AllCaseEqs()`, then in each static case `irule` the matching adapter and discharge assumptions by `simp[]`/existing facts. Do not prove the skeleton bodies in this leaf except by temporary `cheat` if needed to restore buildability.

#### Not to try
Do not keep the old theorem name with the same broad statement; that will invite the same failing proof. Do not move the static split into the adapter skeletons. Do not introduce new global definitions or theory imports.

### C2.1.1.13.4.2: Prove the ordinary static Subscript adapter via a base-success boundary helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The semantic theorem still looks true; E0700 only shows the current proof boundary is too low-level. A helper that consumes the original `eval_expr (Subscript ...)` equality together with the already-known base-success postcondition avoids all direct case-plumbing in the adapter. Remaining work is standard evaluator unfolding inside the helper plus a thin wrapper proof.
- Dependencies: C2.1.1.13.4.1
- Supersedes: C2.1.1.13.4.2
- Progress transition: `refinement`
- Carries progress/evidence from: E0698, E0699, E0700

#### Progress note
E0698's small index helpers remain useful and should be kept. E0699/E0700 invalidate the old direct in-the-adapter proof attempt, but not the ordinary-static theorem statement or the tail/index helper facts. This component is now a grouping node with explicit helper and wrapper leaves.

#### Summary
Replace the brittle direct proof of `expr_subscript_ordinary_static_branch_sound_stmt` with a branch-level boundary helper. The helper owns the evaluator unfolding after the base expression succeeds, including the index evaluation, `get_Value`, and ordinary subscript tail cases. The original adapter should then instantiate the base IH and guarded index IH, call the helper in the base-success branch, and handle base-error propagation directly. Do not change the theorem statement or the already-proved small index helper lemmas.

#### Description
This replaces the prior single Risk-2 leaf, which E0700 showed was underestimated. The new proof interface intentionally prevents the main adapter from stripping or simplifying the full `(case (INL base_tv,st1) of ...) = (res,st')` equality. Instead, the original evaluator equality remains a premise to a local helper that unfolds `Subscript` under the known base-success equality and performs the nested index/get_Value analysis in one focused theorem.

#### Approach
First prove the branch helper in isolation; it may use the same tail helper and index-error helper already in source. Then rewrite the adapter proof so the base-success branch calls this helper before any unfolding of the Subscript evaluator equality. The base-error branch should remain direct propagation using the base IH and one evaluator simplification with the known base-error equality.

#### Not to try
Do not keep varying `Cases_on val_res`, `qpat_assum`/`qpat_x_assum` selection, or manual rewriting of `eval_expr cx e' st1 = ...` in the original adapter; E0699/E0700 show that path remains at the wrong proof boundary. Do not revive the old broad ordinary Subscript helper or push this reasoning back into `Resume eval_all_type_sound_mutual[Expr_Subscript]`; this local adapter split is still the right architecture.

#### Argument
For an ordinary statically-typed subscript expression, after the base expression evaluates successfully to `base_tv` at `st1`, all remaining behavior is a sequential tail: evaluate the index at `st1`; if the index evaluation errors, the index IH supplies preservation and no-TypeError; if it succeeds, call `get_Value`; if `get_Value` errors, the small integer-index helper supplies no-TypeError and `get_Value_state` supplies unchanged state; if `get_Value` succeeds, `expr_subscript_ordinary_tail_sound_stmt` handles bounds checking, `evaluate_subscript`, storage reads, preservation, result typing, and no-TypeError. The main adapter should only split the base evaluation. In the base-success case, the base IH provides `state_well_typed st1`, `env_consistent env cx st1`, accounts well-typedness, and `expr_result_typed env e base_tv`; the guarded index IH is instantiated with the base-success evaluation to produce the unconditional index IH required by the helper. This keeps the induction-recursive facts aligned with the evaluator order and avoids duplicating the subscript tail proof in the outer adapter.

#### Definition design
No semantic definitions should change. The proof interface is a local boundary theorem `expr_subscript_ordinary_base_success_sound_stmt` placed between the existing small index helpers and `expr_subscript_ordinary_static_branch_sound_stmt`. Its critical boundary property is that consumers pass the original `eval_expr cx (Subscript v9 e e') st = (res,st')` equality and the known base-success equality; consumers must not unfold `evaluate_def` for `Subscript` themselves in the base-success branch. Failure sign: if the original adapter proof again contains manual simplification of the full outer `(case (INL ...,...) of ...)` term after the base-success split, the helper interface is not being used correctly.

#### Code structure
Work only in `semantics/prop/vyperTypeStmtSoundnessScript.sml` near the local Subscript helper block around lines 7108-7314. Keep the already-present local helpers `subscript_type_ok_index_is_int_stmt` and `expr_subscript_index_get_Value_INR_no_type_error_stmt`. Insert `expr_subscript_ordinary_base_success_sound_stmt[local]` after those helpers and before `expr_subscript_ordinary_static_branch_sound_stmt`. Then replace the current failed proof body of `expr_subscript_ordinary_static_branch_sound_stmt` with a thin proof that calls the new helper. Do not edit sibling component `expr_subscript_place_as_ordinary_branch_sound_stmt` in this subtree.

### C2.1.1.13.4.2.1: Add and prove the base-success ordinary Subscript helper
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: The helper is a direct evaluator-order proof. All semantic hard cases are already covered by `expr_subscript_ordinary_tail_sound_stmt`, `expr_subscript_index_get_Value_INR_no_type_error_stmt`, the index IH, and `get_Value_state`; the helper mainly packages these facts under the known base-success equality.
- Checkpoint: yes
- Carries progress/evidence from: E0698

#### Progress note
Carries forward the already-added local integer-index/get_Value helper from E0698. This leaf is new because the old component lacked a branch-level boundary theorem.

#### Summary
Introduce a local theorem immediately before `expr_subscript_ordinary_static_branch_sound_stmt`. It assumes the base expression has evaluated to `INL base_tv, st1`, the base-success preservation/typing facts are already available, the guarded index IH has been instantiated into an unconditional index IH, and the original Subscript evaluation equality holds. It concludes the full preservation/no-TypeError/result-typing postcondition for `Subscript v9 e e'`. Prove it by unfolding `evaluate_def` only inside this helper and following evaluator order.

#### Statement
Suggested theorem shape (minor variable names may be adjusted to match HOL):

```sml
Theorem expr_subscript_ordinary_base_success_sound_stmt[local]:
  !cx env e e' v9 base_tv st st1 res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e' /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    eval_expr cx e st = (INL base_tv,st1) /\
    state_well_typed st1 /\ env_consistent env cx st1 /\
    accounts_well_typed st1.accounts /\
    expr_result_typed env e base_tv /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e' st0 = (res0,st0') ==>
      (well_typed_expr env0 e' ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e' = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
```

#### Approach
Start from the final `eval_expr cx (Subscript ...) st = ...` premise, unfold `Once evaluate_def`, and rewrite with `eval_expr cx e st = (INL base_tv,st1)` so the helper owns the tail equality. Split `eval_expr cx e' st1`; instantiate the index IH at `env, st1`; use `well_typed_expr env e'` to get index preservation and, in the success case, `expr_result_typed env e' idx_tv`. Split `get_Value idx_tv st2`: on `INL idx`, use `get_Value_state` and `expr_subscript_ordinary_tail_sound_stmt`; on `INR err`, use `get_Value_state` plus `expr_subscript_index_get_Value_INR_no_type_error_stmt`; on index evaluation `INR`, simplify the evaluator equality and use the index IH's preservation/no-TypeError facts.

#### Not to try
Do not state the helper with the enormous post-base tail expression as an explicit premise unless the compact evaluator-equality form fails; the point is to let the helper rewrite `eval_expr (Subscript ...)` using the base-success equality internally. Do not require `well_typed_expr env e` in this helper unless a tactic genuinely needs it; the helper should consume the already-derived `expr_result_typed env e base_tv` instead of reusing the base IH.

### C2.1.1.13.4.2.2: Reprove `expr_subscript_ordinary_static_branch_sound_stmt` as a thin wrapper
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 10
- Work units: 3
- Rationale: Once the base-success helper exists, the original adapter proof should only split the base evaluation, extract base IH facts, instantiate the guarded index IH, and call the helper. This removes the brittle nested evaluator equality manipulation that caused E0700.
- Dependencies: C2.1.1.13.4.2.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0697, E0698, E0699, E0700

#### Progress note
This replaces the failed direct proof body while preserving the theorem statement installed by C2.1.1.13.4.1. Earlier episodes still support the base-error/base-success split and the small index helpers, but their inner direct proof attempts should not be reused.

#### Summary
Replace the current failed proof of `expr_subscript_ordinary_static_branch_sound_stmt` with a wrapper around `expr_subscript_ordinary_base_success_sound_stmt`. The theorem statement must remain the current source statement at lines 7210-7248. The base-success branch should not unfold the Subscript evaluator; it should pass the original evaluation equality to the helper. The base-error branch can be closed by the base IH and a simple evaluator simplification.

#### Statement
Prove the existing theorem unchanged:

```sml
Theorem expr_subscript_ordinary_static_branch_sound_stmt[local]:
  !cx env e e' v9 st res st'.
    ... (* current statement in vyperTypeStmtSoundnessScript.sml lines 7210-7248 *)
```

#### Approach
In the proof, split `eval_expr cx e st` and instantiate the base IH before unfolding the Subscript evaluation in the base-success case. For `INL base_tv`, derive `state_well_typed st1`, `env_consistent env cx st1`, `accounts_well_typed st1.accounts`, and `expr_result_typed env e base_tv`; instantiate the guarded index IH with the base-success equality to obtain the unconditional index IH; then `irule`/`match_mp_tac` the new base-success helper using the original `eval_expr cx (Subscript v9 e e') st = (res,st')` assumption. For `INR base_err`, unfold `Once evaluate_def` with the base-error equality and use the base IH no-TypeError/preservation facts.

#### Not to try
Do not strip the outer Subscript equality and then split `eval_expr e'` inside this wrapper; that recreates the E0700 failure. Do not manually rewrite named `eval_expr e'` or `get_Value` equalities in this theorem; those cases belong only in the helper from C2.1.1.13.4.2.1.

### C2.1.1.13.4.3: Stabilize and prove the place-as-ordinary Subscript adapter
- Kind: `boundary_lemma_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The prior risk came from an administrative build blocker, not from evidence that the adapter statement is false. Splitting off the BaseTarget_Subscript timeout as a prerequisite leaves only standard local proof/refactor work under this subtree.
- Supersedes: C2.1.1.13.4.3a
- Progress transition: `replacement`
- Carries progress/evidence from: E0704, TO_type_system_rewrite-20260522T073012Z_m40076_t001
- Invalidates prior progress/evidence: C2.1.1.13.4.3@risk3-blocked

#### Progress note
E0704 remains valid evidence that the previous single component was plan-incomplete: holbuild timed out before reaching the adapter. This replacement absorbs that evidence by making the prefix timeout a prerequisite child and resets the parent to an executable risk-2 subtree. The old non-dotted C2.1.1.13.4.3a repair path is superseded by dotted child C2.1.1.13.4.3.1.

#### Summary
This subtree owns only the local work needed to verify `expr_subscript_place_as_ordinary_branch_sound_stmt` inside `vyperTypeStmtSoundnessScript.sml`. First, refactor the already-proved-looking `BaseTarget_Subscript` resume so holbuild no longer times out before the adapter. Then prove the adapter using the ordinary-static projection helper and the existing mutual IHs. No sibling assignment, builtin, call, or wrapper obligations are included here.

#### Description
The source currently contains the adapter skeleton/partial proof near lines 7360-7459 and the consumer in `eval_all_type_sound_mutual[Expr_Subscript]` near lines 7461-7477. The build blocker reported in E0704 is earlier, in `Resume eval_all_type_sound_mutual[BaseTarget_Subscript]`, where a broad simplification after destructing `eval_base_target` causes holbuild to time out. This subtree must make the file build far enough to test the adapter, then close the adapter proof without changing its theorem statement unless the executor reports concrete unprovability evidence.

#### Statement
Primary local target after the prefix refactor:

```sml
Theorem expr_subscript_place_as_ordinary_branch_sound_stmt[local]:
  !cx env e e' v9 base_vt st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e' /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME (Type v9) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    (* mutual IH for e, including place expression conclusion *)
    (* mutual IH for e' after successful evaluation of e *)
    ==> state_well_typed st' /\ env_consistent env cx st' /\
        accounts_well_typed st'.accounts /\ no_type_error_result res /\
        case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
```

#### Approach
Treat the problem as two independent local proof-interface repairs. The first child must be a pure refactor: preserve the `BaseTarget_Subscript` theorem but replace the broad simplifier step with explicit `eval_base_target`/`eval_expr` case splitting and targeted rewrites. The second child proves the adapter by evaluating the base `e`, using the place-expression branch of the IH for `e` to obtain `place_expr_result_typed env base_tv base_vt`, then applying `expr_subscript_place_projection_branch_sound_stmt` with `ordinary_vt = Type v9`; the final conversion to `expr_result_typed` is via `place_expr_result_typed_expr_result_typed_stmt` and `well_typed_expr_def`.

#### Not to try
Do not continue adding tactics to the adapter while holbuild still times out before it; that repeats E0704 and gives no evidence about the adapter. Do not use a broad `simp[bind_def]` or `simp[Once evaluate_def, bind_def]` in `BaseTarget_Subscript` after large assumptions are in context if it expands evaluator conditionals explosively. Do not duplicate the full `Expr_Subscript` evaluator proof in the adapter; the adapter should delegate the ordinary/projection case to the existing local helper and only assemble the IH facts it needs.

#### Argument
For a subscript expression whose base is statically a place expression, the evaluator first evaluates the base expression `e`. If that result is exceptional (`INR`), the whole expression returns that exception and the place-expression IH for `e` already gives state/env/accounts preservation and no `TypeError`. If the base result is a value (`INL base_tv`), the place-expression part of the IH for `e`, instantiated with `base_vt`, gives the runtime shape needed for projection. The static fact `subscript_vtype base_vt (expr_type e') = SOME (Type v9)` and the well-typedness of `e'` allow reuse of the ordinary projection-branch helper, which handles evaluation of the index expression and the runtime subscript operation. Its successful place-typed result is then converted to the normal expression-typed result for `Subscript v9 e e'` using the local conversion lemma and the `well_typed_expr_def` branch for place-as-ordinary subscript.

#### Definition design
No new definitions are intended in this subtree. The proof interface is the existing trio: the mutual IH for `eval_expr`, `expr_subscript_place_projection_branch_sound_stmt`, and `place_expr_result_typed_expr_result_typed_stmt`. The prefix refactor should not expose evaluator internals to downstream consumers; it merely makes the existing `BaseTarget_Subscript` resume robust by using explicit destructuring and targeted rewrites. Failure signs: needing to alter `expr_subscript_place_projection_branch_sound_stmt`, needing a second induction over `eval_expr`, or needing manual theorem plumbing with long `qspecl_then`/`ACCEPT_TAC` blocks beyond instantiating the one projection helper.

#### Code structure
All edits for this subtree belong in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. Child C2.1.1.13.4.3.1 edits only `Resume eval_all_type_sound_mutual[BaseTarget_Subscript]` around lines 6064-6102, preserving the theorem/resume name and conclusion. Child C2.1.1.13.4.3.2 edits only the local adapter theorem `expr_subscript_place_as_ordinary_branch_sound_stmt` around lines 7360-7459, and its immediate consumer only if needed to adjust theorem names after proving the adapter. Do not move helpers to another theory for this local issue.

### C2.1.1.13.4.3.1: Refactor BaseTarget_Subscript to avoid the pre-adapter timeout
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 0
- Work units: 3
- Rationale: The theorem was already conceptually closed in source; the failure is a performance timeout from a broad simplification. A targeted proof script refactor is mechanical and localized.
- Checkpoint: yes
- Supersedes: C2.1.1.13.4.3a
- Progress transition: `replacement`
- Carries progress/evidence from: E0704, TO_type_system_rewrite-20260522T073012Z_m40072_t001

#### Progress note
This is the executable replacement for the previously mentioned C2.1.1.13.4.3a prerequisite. Its completion should resolve the administrative blocker recorded in E0704 by letting holbuild reach the adapter theorem.

#### Summary
Refactor `Resume eval_all_type_sound_mutual[BaseTarget_Subscript]` so holbuild no longer times out before the adapter proof. Preserve the same theorem/resume obligation and do not change downstream statements. The expected check is that `holbuild build vyperTypeStmtSoundnessTheory` progresses past `BaseTarget_Subscript` and reaches the later local adapter if it is still unfinished.

#### Description
The timeout is reported at the first branch after `Cases_on bt_res`, currently near line 6074. The likely cause is a broad `simp[bind_def]` or similar simplification with too many evaluator facts in context. Rewrite this branch to expose only the needed evaluator equations and monadic bind/return facts, rather than asking the simplifier to normalize the entire context.

#### Statement
No new theorem. Refactor the proof of:

```sml
Resume eval_all_type_sound_mutual[BaseTarget_Subscript]:
  ...
QED
```

with the same generated subgoal and conclusion as before.

#### Approach
Use explicit case splits already suggested by the proof: destruct `eval_base_target cx bt st` into `(bt_res,st1)`, apply the base-target IH, then split `bt_res`. In the `INL` location branch, destruct only `eval_expr cx e st1`, apply the expression IH, then destruct `get_Value` and use the existing lemmas `subscript_vtype_index_get_Value_no_type_error`, `location_runtime_typed_rebuild`, and `subscript_vtype_value_step_type`. Keep rewrites targeted: prefer `simp[bind_def, return_def, raise_def]` only after substituting the exact evaluator equation, and avoid adding `AllCaseEqs()` or large definition sets unless the goal is already small.

#### Not to try
Do not run `simp_tac` with `Once evaluate_def, bind_def` over the whole goal after both IHs and typing assumptions are present; that is the reported timeout pattern. Do not add a new lemma outside this subtree for performance unless a minimal local helper is strictly necessary. Do not weaken or skip the `base_target_value_shape_def`/`location_runtime_typed_def` conclusions; the later subscript proof depends on them.

### C2.1.1.13.4.3.2: Prove expr_subscript_place_as_ordinary_branch_sound_stmt
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Once the prefix build reaches this theorem, the proof is a standard adapter over existing local subscript helpers and mutual IHs. The statement matches the consumer in `eval_all_type_sound_mutual[Expr_Subscript]`.
- Dependencies: C2.1.1.13.4.3.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0704

#### Progress note
E0704 shows there is a partial adapter edit in source, but it was not verified. Prior text can be reused as a draft only after C2.1.1.13.4.3.1 lets holbuild reach this theorem.

#### Summary
Close the local adapter theorem that handles the `well_typed_expr` branch where `Subscript v9 e e'` is typed through `type_place_expr env e`. The proof should split on the runtime result of evaluating `e`: success delegates to `expr_subscript_place_projection_branch_sound_stmt`, exception returns via the IH for `e`. The theorem then supports the existing `Expr_Subscript` resume without duplicating evaluator case analysis.

#### Description
This theorem is the bridge from a statically place-typed base to the ordinary expression soundness conclusion for subscript expressions. It should not unfold the complete subscript evaluator beyond the top-level evaluation of `e`; the successful base branch should hand the projection case to `expr_subscript_place_projection_branch_sound_stmt`. The final result type obligation is exactly the conversion from a place-result typing at `Type v9` to expression-result typing for `Subscript v9 e e'`.

#### Statement
Prove the theorem currently in source:

```sml
Theorem expr_subscript_place_as_ordinary_branch_sound_stmt[local]:
  !cx env e e' v9 base_vt st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e' /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME (Type v9) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e st0 = (res0,st0') ==>
      (well_typed_expr env0 e ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    (!s'' tv1 t.
      eval_expr cx e s'' = (INL tv1,t) ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx /\
        eval_expr cx e' st0 = (res0,st0') ==>
        (well_typed_expr env0 e' ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
        !vt.
          type_place_expr env0 e' = SOME vt ==>
          state_well_typed st0' /\ env_consistent env0 cx st0' /\
          accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
          case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
```

#### Approach
Start with `Cases_on eval_expr cx e st` and instantiate the first IH with `env, st, base_res, st1`. In the `INL base_tv` branch, use the place half of that IH with `base_vt`; then instantiate `expr_subscript_place_projection_branch_sound_stmt` with `ordinary_vt = Type v9`, `base_tv`, and state `st1`, passing the second IH for `e'` unchanged after instantiating its leading successful-base premise with `st, base_tv, st1`. After the projection helper returns, split the result conjunctions mechanically; for the `INL` result case, apply `place_expr_result_typed_expr_result_typed_stmt` with witness `Type v9` and discharge the static typing branch by rewriting `well_typed_expr_def` once with `type_place_expr env e = SOME base_vt` and `subscript_vtype ... = SOME (Type v9)`.

#### Not to try
Do not unfold all of `evaluate_def` in the successful-base branch; that is what the projection helper abstracts. Do not try to prove `well_typed_expr env e` from `type_place_expr env e = SOME base_vt`; the theorem only needs the place half of the IH for `e`. Do not manually reconstruct all conjuncts for the projection helper with brittle `first_assum ACCEPT_TAC` lists if a smaller helper-instantiation shape is available; use `irule`/`drule`/`asm_rewrite_tac` and let the assumptions match directly.

### C2.1.1.13.4.3a: Stabilize the BaseTarget_Subscript prefix proof timeout
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 25
- Work units: 1
- Rationale: The failing goal already has the successful base-target equality `eval_base_target cx bt st = (INL (x0,x1),st1)` and the target theorem only needs to expose the monadic bind branch. Replacing the broad `simp[bind_def]` after `PairCases_on x` with a bounded rewrite using the known pair components is a mechanical timeout fix with no semantic change.
- Dependencies: C2.1.1.13.4.2.2

#### Progress note
New authorization added because the checkpoint evidence showed holbuild could not verify the active adapter edit due to an uncovered earlier timeout.

#### Summary
Fix only the timeout at `Resume eval_all_type_sound_mutual[BaseTarget_Subscript]`, around line 6074. Preserve the theorem statement and surrounding proof structure. Replace the broad `PairCases_on x >> simp[bind_def]` normalization with a small, bounded reduction of the successful `(INL (x0,x1),st1)` branch. Confirm `holbuild build vyperTypeStmtSoundnessTheory` proceeds past this resume point far enough to reach later code; if a new semantic subgoal appears, escalate rather than broadening this cleanup.

#### Description
This is a build-verification prerequisite for C2.1.1.13.4.3, not part of the Expr_Subscript mathematical proof. The timeout input goal shows the relevant branch is already specialized to `eval_base_target cx bt st = (INL (x0,x1),st1)` and the remaining antecedent is a case-expression expansion of `bind` for that successful result. Use the existing hypotheses and controlled rewrites to simplify this branch without invoking an expensive global simplifier over `bind_def`. The edit should be minimal and should not introduce cheats, new helper theorems, or statement changes.

#### Statement
No new theorem. Refactor the proof of:

```sml
Resume eval_all_type_sound_mutual[BaseTarget_Subscript]:
  ...
QED
```

at the successful `Cases_on bt_res` branch currently beginning:

```sml
>- (PairCases_on `x` >> simp[bind_def] >> ...)
```

#### Approach
After `Cases_on bt_res`, in the `INL x` branch, avoid asking `simp[bind_def]` to normalize the entire monadic expression from scratch. Destructure `x` only as needed, use the equality already produced by `gvs[]`/the branch context to rewrite to `x0` and `x1`, then unfold only `bind_def`/`return_def` at the top-level case expression. A good proof shape is: pair-destruct, `gvs[bind_def, return_def]` or `simp_tac` with a restricted simp set and the known `eval_base_target` equality, then continue with the existing IH call at lines 6075ff.

#### Not to try
Do not unfold `evaluate_def` again or add `AllCaseEqs()` here; the goal is already past the evaluator split and broad case simplification is what timed out. Do not replace this with a larger `metis_tac` or duplicate the later subscript-value reasoning. Do not edit the active place-as-ordinary adapter while this prefix proof still prevents holbuild from checking it.

### C2.1.1.13.4.4: Integrate adapters and audit Expr_Subscript has no placeholder cheat
- Kind: `proof_integration`
- Risk: 1
- Work priority: 30
- Work units: 2
- Rationale: Once the two adapters are proved, integration is a small Resume rewrite and build/audit check. The proof body should be shorter than the old branch and should not contain semantic case analysis of the subscript tail.
- Dependencies: C2.1.1.13.4.2, C2.1.1.13.4.3
- Checkpoint: yes
- Carries progress/evidence from: C2.1.1.13.4.2, C2.1.1.13.4.3

#### Progress note
This closes the local replacement subtree by removing any temporary cheats introduced in C2.1.1.13.4.1 and verifying the original task-scoped placeholder is gone.

#### Summary
Finalize `Resume eval_all_type_sound_mutual[Expr_Subscript]`. Ensure the ordinary conjunct splits the static Subscript fact and calls the two adapters. Keep the separate place/projection conjunct using the existing place-projection helper. Build `vyperTypeStmtSoundnessTheory` and confirm no `cheat`/`FAIL_TAC` remains in the Expr_Subscript Resume or the new adapters.

#### Statement
No new theorem statement beyond the completed `Resume eval_all_type_sound_mutual[Expr_Subscript]`. Verification target: `holbuild build vyperTypeStmtSoundnessTheory` reaches beyond this theory section with no Expr_Subscript placeholder cheat warning.

#### Approach
Use `qpat_x_assum`/`mp_tac` only to expose the static `well_typed_expr env (Subscript v9 e e')` split. In the ordinary static branch, `irule expr_subscript_ordinary_static_branch_sound_stmt`; in the place-as-ordinary static branch, `irule expr_subscript_place_as_ordinary_branch_sound_stmt`. The remaining place-projection conjunct can stay close to the current source, but remove brittle `pop_assum` state rewrites if the new adapters make them unnecessary.

#### Not to try
Do not reintroduce a direct call to the deleted broad helper. Do not accept a build that still contains temporary skeleton cheats in the new adapters or any `FAIL_TAC` probe around Expr_Subscript. Do not broaden this audit to unrelated `Expr_Attribute`, builtin, or call cheats; those are separate task components.

### C2.1.1.5: Carry forward completed Iterator_Range repair for external dependency compatibility
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 5
- Work units: 0
- Rationale: This ID is intentionally preserved because C2.2 has depended on it. The associated repair was already proved, so this is a schema-safe placeholder rather than executable work.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.1.5, E0656

#### Summary
- Preserves the externally referenced `C2.1.1.5` ID.
- Carries completed Iterator_Range repair evidence.
- Prevents dangling dependency validation failures in C2.2.
- No source edits or builds are required for this node.

#### Statement
No new theorem statement; existing repaired branch remains in source.

#### Approach
If the harness asks for closure, cite/build evidence that the Iterator_Range repair was already completed. Otherwise do not touch the source.

#### Not to try
Do not delete or rename this component ID while C2.2 still depends on it.

### C2.1.1.8: Carry forward completed Expr_BareGlobalName proof-order repair
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 8
- Work units: 0
- Rationale: The BareGlobalName Resume repair was already proved and is retained as completed progress under the rebased parent.
- Dependencies: C2.1.1.5
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.1.8, E0657

#### Summary
- No executor work.
- Carries completed `Expr_BareGlobalName` split/strip repair.
- Maintains chronological proof progress toward the current Subscript branch.
- Do not reopen unless a later build regresses here.

#### Statement
No new theorem statement; existing `Resume eval_all_type_sound_mutual[Expr_BareGlobalName]` remains proved.

#### Approach
No action. If regression evidence appears, escalate separately rather than editing under this placeholder.

#### Not to try
Do not combine BareGlobalName with the active Subscript repair.

### C2.1.1.9: Carry forward completed Expr_TopLevelName proof-order repair
- Kind: `carried_evidence`
- Risk: 1
- Work priority: 9
- Work units: 0
- Rationale: The TopLevelName Resume repair was already proved and is retained as completed progress.
- Dependencies: C2.1.1.8
- Progress transition: `carry_forward`
- Carries progress/evidence from: C2.1.1.9, E0659

#### Summary
- No executor work.
- Carries completed `Expr_TopLevelName` proof-order repair.
- Keeps the rebased expression repair sequence intact.
- Only Subscript is active now.

#### Statement
No new theorem statement; existing `Resume eval_all_type_sound_mutual[Expr_TopLevelName]` remains proved.

#### Approach
No action unless holbuild unexpectedly regresses at this branch.

#### Not to try
Do not reopen TopLevelName while repairing Subscript.

### C2.2: Close the Expr_Attribute read/path resume after Iterator_Range and Expr_Subscript repairs
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: This is the same Expr_Attribute consumer obligation as before, but it must not be authorized while the source fails earlier in the mutual theorem at Iterator_Range. Adding the dependency is scheduling/consistency repair, not a change to the proof strategy.
- Dependencies: C2.1.1.5
- Progress transition: `refinement`
- Carries progress/evidence from: C2.2

#### Progress note
C2.2 is unchanged semantically but is re-gated behind the new Iterator_Range cleanup so the executor cannot start it while the current build frontier is earlier.

#### Summary
- Same Expr_Attribute read/path resume as previously planned.
- Now depends on C2.1.1.5 because Iterator_Range is the current earlier build frontier.
- Use the strengthened expression IH shape after both Subscript and Iterator_Range are clean.

#### Description
This update only fixes scheduling after E0643. Expr_Attribute remains a later structural expression consumer, but the current source must first build past Iterator_Range.

#### Approach
After C2.1.1.5, resume the previous Expr_Attribute plan: project the relevant expression/place IH facts and avoid broad simplification over the full strengthened context.

#### Not to try
Do not begin Expr_Attribute while `holbuild build vyperTypeStmtSoundnessTheory` still fails at Iterator_Range.

### C2.3: Close `Expr_Pop` using assignment/subscript preservation interfaces
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: `Pop` is the one remaining stateful non-call expression case and should be a consumer of the C3 assignment-subscript no-TypeError/preservation chain. With C3 complete, the branch is a local evaluator replay.
- Dependencies: C2.0, C3.3

#### Progress note
Scheduled after C3 because `Pop` follows the update/subscript leaf path named in the task handover.

#### Summary
- Replace the `Expr_Pop` cheat.
- Depend on C3 recursive assignment-subscript no-TypeError/preservation lemmas.
- Preserve all-result state/account typing through the C3 operation interfaces.
- Keep the branch proof local to the evaluator constructor.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Pop]: ... QED
```

#### Approach
After one-step evaluator unfolding, use the IHs for target/path evaluation and then apply C3's `assign_subscripts_no_type_error_runtime_typed` / preservation counterpart for the pop operation. The success result must show both the popped value has the expression type and the post-state remains well typed/accounts well typed.

#### Not to try
Do not re-prove recursive `assign_subscripts` facts inside the statement mutual proof. Do not weaken the assignment operation side conditions introduced by C1/C2 assignment repairs.

### C2.4: Close builtin expression resume
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: Once C4 closes builtin no-TypeError and success-typing residuals, the expression case is a direct argument-evaluation and boundary-lemma application.
- Dependencies: C2.1, C2.2, C4.2

#### Progress note
New C2 consumer of C4 builtin boundary theorems.

#### Summary
- Replace the `Expr_Builtin` cheat.
- Use `eval_exprs` IH for argument list soundness.
- Apply C4 builtin no-TypeError/success-typing theorem instead of unfolding builtin semantics.
- Preserve state facts through argument evaluation and pure builtin execution.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Builtin]: ... QED
```

#### Approach
Unfold the expression evaluator to the argument evaluation and builtin application. From the `eval_exprs` IH obtain no-TypeError and `exprs_runtime_typed`; then instantiate `well_typed_builtin_app_no_type_error` and `well_typed_builtin_app_success_type` (or their final C4 names) to discharge the result obligations.

#### Not to try
Do not expand `evaluate_builtin_def` in this resume except for a trivial wrapper mismatch. Any missing builtin constructor case is a C4 dependency, not a C2 proof search problem.

### C2.5: Close type-builtin expression resume
- Kind: `proof`
- Risk: 2
- Work priority: 50
- Work units: 5
- Rationale: The type-builtin expression branch is the same consumer pattern as ordinary builtins but depends on the C4 type-builtin no-TypeError and ABI/success typing facts.
- Dependencies: C2.4, C4.3, C4.4, C4.5

#### Progress note
New C2 consumer of C4 type-builtin boundary theorems.

#### Summary
- Replace the `Expr_TypeBuiltin` cheat.
- Use argument IHs plus C4 type-builtin interfaces.
- Handle ABI encode and raw-call/type-size side conditions only through C4 lemmas.
- Keep the statement mutual proof free of type-builtin case explosions.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_TypeBuiltin]: ... QED
```

#### Approach
Evaluate arguments with the mutual IH and convert the static `well_typed_expr_def` facts into C4's `well_typed_type_builtin_args` premises. Apply C4 no-TypeError and success-typing lemmas to show the returned value has the evaluated expression type.

#### Not to try
Do not locally prove ABI encode bounds or MsgGas/raw-call arithmetic in `vyperTypeStmtSoundnessScript.sml`; those are C4-owned facts.

### C2.6: Close external and special call-target expression resumes
- Kind: `proof`
- Risk: 2
- Work priority: 60
- Work units: 8
- Rationale: These call targets do not evaluate a Vyper function body, so after C4 raw-call/builtin facts they are finite evaluator branches over already-evaluated arguments and target-specific well-typedness conditions.
- Dependencies: C2.5, C4.5

#### Progress note
New C2 work for non-internal `Expr_Call_*` resumes; C5 wrappers cannot be used because of theory order.

#### Summary
- Replace cheats for `Expr_Call_ExtCall`, `Expr_Call_Send`, `Expr_Call_RawCallTarget`, `Expr_Call_RawLog`, `Expr_Call_RawRevert`, `Expr_Call_SelfDestructTarget`, and `Expr_Call_CreateTarget`.
- Use argument/driver expression IHs and C4 raw/special-call no-TypeError facts.
- Prove only statement-theory expression result obligations; public wrappers remain C5.
- Avoid any import from `vyperTypeCallSoundness`.

#### Statement
Resume blocks:
```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_Send]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_RawLog]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_RawRevert]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_SelfDestructTarget]: ... QED
Resume eval_all_type_sound_mutual[Expr_Call_CreateTarget]: ... QED
```

#### Approach
Handle each constructor by one-step evaluator unfolding, then evaluate target/argument subexpressions with IHs. Use C4 special/raw-call no-TypeError and success-type facts for the primitive operation; for exceptional branches, show `stmt_error_ok`/no-TypeError via the mutual theorem's result predicates and existing exception typing definitions.

#### Not to try
Do not call `external_call_no_type_error` or `special_call_no_type_error` from `vyperTypeCallSoundnessScript.sml`; those wrappers are downstream and unavailable. Do not duplicate internal-call body reasoning in these non-body cases.

### C2.7: Prove non-circular internal-call support and close `Expr_Call_IntCall`
- Kind: `proof_group`
- Risk: 2
- Work priority: 70
- Work units: 0
- Rationale: Internal calls are the only remaining C2 case with recursive statement-body evaluation. Splitting call-frame extraction, argument/default binding, and body/restore integration keeps each leaf a standard consumer of existing invariants and the mutual IH.
- Dependencies: C2.6
- Checkpoint: yes

#### Progress note
New subtree for internal calls inside statement soundness; avoids the circular C5 wrapper route.

#### Summary
- Build the internal-call proof inside `vyperTypeStmtSoundness`, not through C5.
- Extract any needed function-body typing helper from the current call-wrapper layer into the statement file/lower theory.
- Prove call-frame env consistency from argument/default runtime typing.
- Use the statement-list IH for the called body and scope-pop restoration for the caller state.

#### Description
This parent is non-executable; prove its children in order. Checkpoint after C2.7.3 because internal-call closure is the key architectural validation for statement/expression soundness.

#### Not to try
Do not import or depend on `vyperTypeCallSoundness`. Do not prove a second top-level internal-call soundness theorem by induction outside `eval_all_type_sound_mutual`; wrappers can be projections later in C5.

#### Argument
Internal call evaluation follows the evaluator recursion: evaluate supplied arguments, evaluate defaults if needed, create a call frame/scope, evaluate the callee body with `eval_stmts`, and restore/pop the frame on return. The static counterpart is `functions_well_typed`: it provides the callee body environment, return type evaluation, parameter/default typing, and body typing. The mutual IH is strong enough because it includes expression-list soundness for argument/default evaluation and statement-list soundness for the body under the callee environment. Frame preservation lemmas provide the bridge back to the caller state/env after the body returns.

#### Definition design
The helper interface must avoid C5. If `functions_well_typed_body` currently exists only in `vyperTypeCallSoundnessScript.sml`, recreate/extract a non-circular version before the mutual proof in `vyperTypeStmtSoundnessScript.sml` with the same conclusion shape needed by the call branch. Call-frame helpers should conclude concrete `env_consistent env_body cx st_frame`, parameter lookup facts, and static map equalities, not require the resume proof to reconstruct them by large `FLOOKUP` plumbing.

#### Code structure
Place C2.7.1/C2.7.2 helpers before the `eval_all_type_sound_mutual` resume section in `vyperTypeStmtSoundnessScript.sml`. The final C2.7.3 edit replaces only the `Expr_Call_IntCall` resume. If a helper is also useful for C5, leave it exported from `vyperTypeStmtSoundnessTheory` so `vyperTypeCallSoundness` can import it later.

### C2.7.1: Expose callee body typing facts in a non-circular helper
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 3
- Rationale: A nearly identical helper exists in the call wrapper layer; moving/recreating it before the statement mutual proof is standard map/projection work from `functions_well_typed_def`.
- Dependencies: C2.6

#### Progress note
New helper to avoid C5 theory-cycle dependency.

#### Summary
- Add a statement-layer helper equivalent to `functions_well_typed_body`.
- Derive callee env, return type value, body typing, default typing, and parameter assignability facts.
- Keep the conclusion directly usable by `Expr_Call_IntCall`.
- Prefer reusing the current proof from `vyperTypeCallSoundnessScript.sml` if source order allows moving it.

#### Statement
Shape to add before the mutual proof (names may follow source conventions):
```sml
Theorem functions_well_typed_body_stmt:
  functions_well_typed cx /\ fn_sigs_consistent fn_sigs cx /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,args,dflts,ret,body) /\
  <same static map consistency premises needed by env_consistent> ==>
  ?env_body ret_tv env_after.
    env_body.current_src = src /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = fn_sigs /\ env_body.bare_globals = bare_globals /\
    env_body.toplevel_vtypes = toplevel_vtypes /\ env_body.flag_members = flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret body = SOME env_after /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T)
```

#### Approach
Start from the existing `functions_well_typed_body` proof in `vyperTypeCallSoundnessScript.sml` and relocate/adapt it without adding a new theory dependency. The proof should be `rw[functions_well_typed_def]`, apply the function body well-typedness premise, and package the witnesses.

#### Not to try
Do not make `vyperTypeStmtSoundness` import `vyperTypeCallSoundness`. Do not inline this projection inside `Expr_Call_IntCall`; it will create unreadable theorem plumbing.

### C2.7.2: Prove call-frame environment consistency from evaluated arguments/defaults
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: This is frame/env consistency bookkeeping using existing env extension, scope push/pop, and expression-list runtime typing facts. It is necessary to make the final internal-call resume use `drule` rather than manual map reconstruction.
- Dependencies: C2.7.1

#### Progress note
New interface helper for internal call branch.

#### Summary
- Add one or more helpers converting typed argument/default values into a callee `env_consistent` frame.
- Include parameter `var_types`/`var_assignable` lookup facts in the assumptions/conclusion.
- Preserve static maps (`type_defs`, `fn_sigs`, globals, flags) from caller to callee.
- The final conclusion should be directly consumable by the body `eval_stmts` IH.

#### Statement
Exact statement may be split, but the final helper should have this use-site shape:
```sml
Theorem internal_call_frame_env_consistent:
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  functions_well_typed cx /\ accounts_well_typed st.accounts /\
  <callee env_body/static-map facts from C2.7.1> /\
  <evaluated argument/default values match parameter types> /\
  <call-frame construction in evaluator yields st_frame> ==>
  env_consistent env_body cx st_frame /\ state_well_typed st_frame /\
  accounts_well_typed st_frame.accounts
```

#### Approach
Let the actual evaluator call-frame definitions determine whether this is one lemma or two (argument binding and pushed-scope consistency). Use existing `vyperTypeEnvExtension`, `vyperTypeEnvPreservation`, `vyperTypeScopePop`, and scope preservation lemmas; avoid unfolding `env_consistent_def` in the final resume.

#### Not to try
Do not manually instantiate long `FLOOKUP`/`ALOOKUP` facts in the final call proof. If the helper requires copying entire assumptions into `ASSUME` terms, strengthen/split the helper instead.

### C2.7.3: Close the `Expr_Call_IntCall` mutual-proof resume
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: With callee body typing and call-frame consistency helpers in place, the resume follows the evaluator order and uses the existing mutual IH for argument/default expressions and callee body statements.
- Dependencies: C2.7.2
- Checkpoint: yes

#### Progress note
Checkpoint leaf: confirms the strongest-joint-invariant architecture handles recursive internal calls without C5 wrappers.

#### Summary
- Replace the `Expr_Call_IntCall` cheat.
- Evaluate args/defaults with expression-list IHs.
- Use C2.7.1/C2.7.2 to enter the callee body environment.
- Invoke statement-list IH on the body and restore caller-frame invariants.
- Record checkpoint evidence before final C2 audit.

#### Statement
```sml
Resume eval_all_type_sound_mutual[Expr_Call_IntCall]: ... QED
```

#### Approach
Follow `evaluate_def` order exactly. After the callee lookup and signature/body facts, apply C2.7.1. Use the IHs for `eval_exprs` of arguments/defaults to rule out TypeError and obtain runtime-typed values. Apply C2.7.2 to get callee `env_consistent`, then use the `eval_stmts` IH for the body; finally use existing scope-pop/restore lemmas to discharge caller-state preservation and result typing.

#### Not to try
Do not use C5 `internal_call_no_type_error` or `internal_call_type_preservation`. Do not split this into separate no-TypeError and preservation proofs; the mutual IH already gives the joint result.

### C2.8: Audit `vyperTypeStmtSoundnessTheory` for build success and zero local cheats
- Kind: `build_audit`
- Risk: 1
- Work priority: 80
- Work units: 1
- Rationale: After all expression resumes are proved, local validation is mechanical: build the statement theory and grep the statement file for remaining literal cheats.
- Dependencies: C2.3, C2.7.3
- Checkpoint: yes

#### Progress note
New terminal C2 audit replacing old C2.4, which audited only the assignment-repair subset.

#### Summary
- Run `holbuild build vyperTypeStmtSoundnessTheory`.
- Grep `vyperTypeStmtSoundnessScript.sml` for literal `cheat`.
- Confirm all old and new C2-owned resumes are closed.
- If remaining cheats are in C3/C4/C5 files, report them as sibling work, not C2 failures.

#### Statement
Validation commands:
```sh
holbuild build vyperTypeStmtSoundnessTheory
grep -n '\bcheat\b' semantics/prop/vyperTypeStmtSoundnessScript.sml
```

#### Approach
This component should not require proof edits. If the build fails in a C2 resume, close a stuck/progress episode with the exact theorem and goal; if it fails in C3/C4 prerequisites, follow that sibling component instead.

#### Not to try
Do not chase cheats in retired old theories or in `vyperTypeBuiltinsScript.sml`/`vyperTypeCallSoundnessScript.sml` under this component; those are covered by C4/C5 unless they block the statement-theory build.

### C3: Update-binop and assignment-subscript runtime-typed path
- Kind: `proof_group`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: The inherited cheats form a localized dependency chain from binop no-TypeError through update assignment leaf and recursive subscript preservation.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3

#### Progress note
Replaces the old high-risk inherited path gate with an explicit linear chain of low-risk theorem families.

#### Summary
Prove the known inherited update-binop path: `well_typed_binop_no_type_error`, `well_typed_update_binop_no_type_error`, `assign_subscripts_update_leaf_no_type_error`, `assign_operation_runtime_typed_leaf_no_type_error`, `assign_subscripts_no_type_error_runtime_typed`, and `assign_subscripts_preserves_type_runtime_typed`. Keep the work localized to builtin/binop and assignment-subscript lemmas.

#### Approach
Prove bottom-up: binop, update-binop, leaf assignment operation, then structural/recursion induction over subscript assignment. Use the induction principles generated for recursive functions where available.

#### Not to try
Do not treat the inherited cheats as statement-level issues. Do not duplicate all binop cases inside `assign_subscripts`; delegate to the binop/update leaf theorem.

#### Argument
Update assignment reaches a leaf operation that evaluates a typed binary operation on the old leaf value and RHS value. The binop theorem excludes TypeError for statically well-typed operands; the update-binop theorem packages that for assignment update operations. Recursive subscript assignment preserves no-TypeError and type by induction over the subscript path: prefix traversal preserves the leaf type, the leaf operation is sound, and the result is reinserted into a value of the original type.

#### Definition design
The proof interface should remain: static binop typing + runtime operand typing -> no TypeError/success type; assignment operation runtime typed + leaf typed -> operation no TypeError/success type; target path typed + root value typed -> recursive subscript no TypeError/preservation. If a recursive subscript proof needs an operation-specific fact, add it at the leaf-operation boundary, not by special-casing every subscript constructor.

#### Code structure
Binop lemmas belong in `vyperTypeBuiltinsScript.sml` near existing `well_typed_binop_*`. Assignment-subscript and operation leaf lemmas belong in `vyperTypeStatePreservationScript.sml` near existing `assign_subscripts_*` helpers. Do not move these into statement soundness.

### C3.1: Close binop no-TypeError lemmas
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: Case analysis over binop/type constructors is finite and already supported by success typing lemmas.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3.1

#### Progress note
Same theorem family as prior C3.1, now explicitly first in the update path.

#### Summary
Prove `well_typed_binop_no_type_error` and use it to prove `well_typed_update_binop_no_type_error` in `vyperTypeBuiltinsScript.sml`.

#### Statement
`Theorem well_typed_binop_no_type_error` and `Theorem well_typed_update_binop_no_type_error` in current source.

#### Approach
Split on the binop and the well-typed-binop relation. Use existing evaluator definitions, integer bound lemmas, decimal/wrapped operation no-error facts, and `well_typed_binop_success_type` where it supplies inversions. Keep arithmetic goals local with existing bound lemmas.

#### Not to try
Do not prove success typing and no-TypeError by separate exhaustive duplicated scripts if one helper can share case analysis. Do not leave update-binop as a wrapper over a cheated binop theorem.

### C3.2: Close assignment operation leaf no-TypeError for update/append/pop/plain assign
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 5
- Rationale: Leaf operation soundness is a small case split on assignment operation, with C3.1 handling update-binop.
- Dependencies: C3.1
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3.2

#### Progress note
First assignment-side consumer of the binop theorem.

#### Summary
Prove `assign_subscripts_update_leaf_no_type_error` and `assign_operation_runtime_typed_leaf_no_type_error` without cheats. These exclude TypeError at the leaf operation under `assign_operation_runtime_typed` and operation-shape hypotheses.

#### Statement
Current-source theorems named `assign_subscripts_update_leaf_no_type_error` and `assign_operation_runtime_typed_leaf_no_type_error` in `vyperTypeStatePreservationScript.sml`.

#### Approach
Case split on the assignment operation. Plain assignment is direct from value typing; update uses C3.1; append/pop use the strengthened dynamic-array requirement in `assign_operation_runtime_typed` to rule out wrong-shape TypeError. Keep success typing facts available for the preservation component.

#### Not to try
Do not hide append/pop shape requirements in simplification. If pop/append fail, inspect `assign_operation_runtime_typed` first rather than weakening the theorem.

### C3.3: Close recursive assignment-subscript no-TypeError and preservation
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: This is the structural recursive consumer of C3.2 and existing target-path typing lemmas.
- Dependencies: C3.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C3.2

#### Progress note
Completes the task-listed inherited update-binop path.

#### Summary
Prove `assign_subscripts_no_type_error_runtime_typed` and `assign_subscripts_preserves_type_runtime_typed` without inherited cheats. Use recursive subscript/path induction and the leaf operation theorem at the base.

#### Statement
Current-source theorems named `assign_subscripts_no_type_error_runtime_typed` and `assign_subscripts_preserves_type_runtime_typed` in `vyperTypeStatePreservationScript.sml`.

#### Approach
Use the induction principle for `assign_subscripts`/path recursion if available; otherwise induct on the subscript list in the direction matching the function. At each path step, use `target_path_step_type` to prove the traversal cannot raise TypeError and preserves the expected leaf type. At the base, invoke C3.2.

#### Not to try
Do not unfold all storage/top-level target cases here; this theorem is about recursive value subscript assignment, not top-level lookup.

### C4: Builtin, type-builtin, and builtin-typing soundness residuals
- Kind: `proof_group`
- Risk: 2
- Work priority: 40
- Work units: 0
- Rationale: Current source isolates builtin residuals to a finite set of constructor branches and small arithmetic/ABI facts. The ABI encode bound has already been added to the typing predicate, removing the old spec gap.
- Required for completion: yes
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4

#### Progress note
Keeps all task-listed builtin/binop/type-builtin cheats in one subsystem, with binop update path delegated to C3.

#### Summary
Remove reachable cheats in `vyperTypeBuiltinsScript.sml` and strict prerequisite fresh builtin-typing theories. This includes generic builtin no-TypeError/success typing residuals, type-builtin no-TypeError, ABI encode success branches, raw-call return type well-formedness, and Env/MsgGas-related issues if still reachable.

#### Approach
Close static typing prerequisites first if C0 shows them reachable, then generic builtin cases, then type-builtin no-TypeError/success branches. Use existing specialized lemmas such as bytes/crypto/ABI helpers instead of unfolding encoders deeply in every case.

#### Not to try
Do not re-open the old ABI encode unprovability gate unless current source lacks the `vyper_abi_size_bound` repair. Do not treat binop update-assignment cheats here; those are C3.

#### Argument
Builtin soundness is by constructor case analysis: the static typing predicate constrains argument lengths/types and result type; runtime argument typing plus specialized evaluator lemmas show no TypeError and success value typing. Type-builtins are similar but use `type_builtin_result_ok`; ABI encode branches now rely on its `vyper_abi_size_bound` condition to prove bytes length bounds. Raw-call return type well-formedness is arithmetic over `word_size`, `type_slot_size`, and the max-outsize bound.

#### Definition design
Use existing static predicates (`well_typed_builtin_app`, `well_typed_type_builtin_args`, `type_builtin_result_ok`) as the boundary. Do not add ad hoc side conditions in the final wrappers unless the source theorem is demonstrably underspecified; if underspecified, prove a small probe/counterexample before changing a theorem. Failure sign: ABI encode success typing cannot prove bytes length; this should be solved from `vyper_abi_size_bound`, not by weakening `value_has_type`.

#### Code structure
Builtin proofs stay in `semantics/prop/vyperTypeBuiltinsScript.sml`. If C0 shows reachable suspends in `vyperBuiltinTypingScript.sml`, close them there as static typing prerequisites only. Do not mix builtin proofs into statement or call soundness files.

### C4.1: Close reachable `vyperBuiltinTyping` suspended cases
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These are static constructor cases over builtin typing and only required if C0 proves they are reachable.
- Dependencies: C0
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.1

#### Progress note
Conditional leaf: execute only for C0-reported reachable suspends in `vyperBuiltinTypingScript.sml`.

#### Summary
If `vyperBuiltinTypingScript.sml` suspended builtin typing cases are reachable from `vyperSemanticsHolTheory`, prove exactly those cases. Cases include Len/Not/Neg/Abs/crypto/Env/Acc/etc. as reported by audit.

#### Statement
C0-reported reachable suspended cases in `semantics/prop/vyperBuiltinTypingScript.sml`, especially the large builtin typing case split around `suspend "Len"` etc.

#### Approach
For each constructor, unfold the static typing definition and prove the required result type/argument constraints. Prefer one constructor per edit/build cycle. If a case depends on a runtime semantic fact, that is a sign it belongs in `vyperTypeBuiltinsScript.sml`, not this static layer.

#### Not to try
Do not prove all grep-reported suspends if the theory is not reachable. Do not import runtime soundness theories into static builtin typing.

### C4.2: Close generic builtin no-TypeError and success typing residuals
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: The current proof skeleton already closes most constructors and has explicit fallback points for remaining branches.
- Dependencies: C4.1
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.2

#### Progress note
Covers the cheat near the end of the generic builtin success/no-error proof skeleton, excluding type-builtins handled by C4.3-C4.4.

#### Summary
Remove the generic builtin proof cheat in `vyperTypeBuiltinsScript.sml` around the large builtin soundness case split. Close Env/Acc/crypto/bytes/arithmetic residuals with existing specialized lemmas.

#### Statement
Current-source generic builtin theorem(s) around line ~2380-2411 of `vyperTypeBuiltinsScript.sml`, including any C0-reported cheat in the proof of builtin success typing/no-TypeError before `Len_result_fits_uint256`.

#### Approach
Identify the exact constructor left by the final `cheat` by temporarily replacing it with `NO_TAC` if needed. Then add a branch-specific lemma or direct call to existing helpers (`Env_builtin_success_type`, `Acc_builtin_sound`, bytes/crypto length lemmas, bounded/wrapped op inversions). Keep arithmetic to small subgoals.

#### Not to try
Do not leave a catch-all `cheat` after many `TRY` tactics; each remaining constructor must be named and closed. Do not use broad `metis_tac` over all builtin lemmas if it obscures a missing side condition.

### C4.3: Prove type-builtin no-TypeError
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: No-TypeError follows by constructor case analysis using argument length/type constraints and context well-typedness.
- Dependencies: C4.1
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.3

#### Progress note
Covers `well_typed_type_builtin_no_type_error` specifically.

#### Summary
Remove the cheat from `well_typed_type_builtin_no_type_error` in `vyperTypeBuiltinsScript.sml`. Use `well_typed_type_builtin_args_length` and the same constructor split as success typing.

#### Statement
`Theorem well_typed_type_builtin_no_type_error` in current source.

#### Approach
Split on `tb`, unfold `evaluate_type_builtin_def`, `type_builtin_result_ok_def`, and `well_typed_type_builtin_args_def` only for the active constructor. For conversions/extract/ABI cases, use existing no-error facts from conversion/ABI helper theories; if only success-typing helpers exist, prove a small no-TypeError analogue locally.

#### Not to try
Do not rely on success typing theorem alone to prove no-TypeError unless the evaluator equation is already known to be `INL`. Do not add assumptions beyond current theorem without a checked false-statement probe.

### C4.4: Prove ABI encode type-builtin success branches
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: The old ABI bound gap is repaired in `type_builtin_result_ok`, so the three suspended/cheated branches are now finite consumers of ABI bound lemmas.
- Dependencies: C4.3
- Checkpoint: yes
- Supersedes: old ABI encode result-bound gap
- Progress transition: `refinement`
- Carries progress/evidence from: TYPE_SYSTEM_REWRITE_PLAN ABI bound repair note

#### Progress note
Supersedes the stale unprovability concern by using the current source’s `vyper_abi_size_bound` side condition.

#### Summary
Finish `well_typed_type_builtin_success_type[abi_encode]`, `[encode_tuple]`, and `[encode_tuple_nowrap]`. Prove the result `BytesT`/ABI value typing from encoder success and the bound carried by `type_builtin_result_ok`.

#### Statement
`Resume well_typed_type_builtin_success_type[abi_encode]`, `[encode_tuple]`, and `[encode_tuple_nowrap]` in current `vyperTypeBuiltinsScript.sml`.

#### Approach
Unfold the active type-builtin case, extract `vyper_abi_size_bound` from `type_builtin_result_ok`, and use ABI encode length/success typing lemmas to prove the returned bytes/string value fits the result type. If a length lemma is missing, add it next to existing ABI helper lemmas as a strict prerequisite.

#### Not to try
Do not weaken the result type to dynamic bytes without checking the theorem statement. Do not ignore the bound side condition; it is the intended repair.

### C4.5: Close raw-call return type well-formedness and Env/MsgGas support
- Kind: `proof`
- Risk: 2
- Work priority: 40
- Work units: 5
- Rationale: The remaining raw-call theorem is arithmetic over `word_size` and type slot size; Env/MsgGas issues are local builtin constructor facts.
- Dependencies: C4.2
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C4.4

#### Progress note
Covers task-mentioned Env MsgGas issues and the visible `raw_call_return_type_well_formed` cheat.

#### Summary
Remove the cheat from `raw_call_return_type_well_formed` and close any remaining Env/MsgGas builtin support theorem reported by C0. These support special-call and builtin soundness wrappers.

#### Statement
`Theorem raw_call_return_type_well_formed` in `vyperTypeBuiltinsScript.sml`, plus any C0-reported reachable Env/MsgGas builtin helper cheat in the same file.

#### Approach
For raw-call, case split on flags and reduce to `word_size_le`, `type_slot_size_def`, and simple natural arithmetic under `flags.rcf_max_outsize < dimword(:256)`. For Env/MsgGas, unfold the relevant builtin evaluator/static typing branch and use context well-typedness fields that type gas/message values.

#### Not to try
Do not solve raw-call by assuming `word_size n < n`; the source already has the split and needs the equality case closed correctly. Do not add global context assumptions to special-call wrappers unless current Env builtin theorem is false and a probe confirms it.

### C5: Call wrapper soundness
- Kind: `proof_group`
- Risk: 2
- Work priority: 50
- Work units: 0
- Rationale: Call wrappers are downstream consumers of expression/statement/builtin soundness and function signature consistency; they do not require a new evaluator induction.
- Required for completion: yes
- Dependencies: C2, C4
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5

#### Progress note
Keeps the task-listed call wrapper cheats explicit and downstream of statement/builtin soundness.

#### Summary
Prove `internal_call_no_type_error`, `internal_call_type_preservation`, `external_call_no_type_error`, and `special_call_no_type_error` in `vyperTypeCallSoundnessScript.sml`. These are wrappers around existing argument/default/body/special-target soundness facts.

#### Approach
Prove external/special wrappers first because they avoid body recursion. Then internal no-TypeError and preservation using the same decomposition. Keep no-TypeError and preservation wrappers as projections from statement/expression joint results rather than duplicating call evaluator case analysis.

#### Not to try
Do not unfold the full statement evaluator inside call wrappers. Do not create an import cycle by making statement soundness depend on call soundness.

#### Argument
For internal calls, static expression typing gives a function signature and argument bounds; `fn_sigs_consistent` and `functions_well_typed_body` recover the callable body typing environment, defaults typing, parameter types, and return type. Argument and default evaluation soundness establish the call-entry state/env invariants; statement soundness for the body excludes TypeError and preserves state/return typing. External and special calls do not recurse into a Vyper body, so they reduce to argument/driver expression soundness and builtin/special-target no-TypeError facts.

#### Definition design
The call proof boundary is wrapper-level: `well_typed_expr ... Call ...` plus `env_consistent`, `state_well_typed`, `context_well_typed`, `accounts_well_typed`, and for internal calls `functions_well_typed`. Do not strengthen public call wrappers unless a checked false-statement probe shows a missing prerequisite. If internal preservation needs return-value typing not exported by statement soundness, add a statement corollary projection rather than re-inducting over statements here.

#### Code structure
All call wrapper edits belong in `semantics/prop/vyperTypeCallSoundnessScript.sml`. Helper lemmas about function signatures/defaults can live near existing `fn_sig_argument_bounds`, `defaults_env_erases_locals`, and `functions_well_typed_body`. Do not create imports from call soundness back into statement soundness.

### C5.1: External and special call no-TypeError wrappers
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 5
- Rationale: These wrappers avoid internal function body recursion and reduce to argument/driver and builtin/special-target facts.
- Dependencies: C4.5
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5.1

#### Progress note
Same external/special wrapper obligation as pre-collapse plan.

#### Summary
Prove `external_call_no_type_error` and `special_call_no_type_error` in `vyperTypeCallSoundnessScript.sml`. Use expression argument soundness, optional driver soundness, and special-target builtin support.

#### Statement
`Theorem external_call_no_type_error` and `Theorem special_call_no_type_error` in current source.

#### Approach
Case split on the call target only as much as the theorem statement already distinguishes. Use `ext_call_args_typed` for external calls and current special-call/static builtin facts for the rest. Project `no_type_error_eval` from the expression/builtin soundness theorem used by the evaluator branch.

#### Not to try
Do not try to prove internal call facts in the special-call theorem; the hypotheses explicitly exclude `IntCall` and `ExtCall` for `special_call_no_type_error`.

### C5.2: Internal call no-TypeError wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 10
- Work units: 8
- Rationale: Existing helper lemmas recover function body typing and argument/default alignment; statement soundness supplies body no-TypeError.
- Dependencies: C2.3, C5.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5.2

#### Progress note
Same theorem as source; proof is authorized after statement soundness is stable.

#### Summary
Prove `internal_call_no_type_error`. Decompose call evaluation into argument evaluation, defaults/parameter setup, body evaluation, and return handling; each phase consumes existing soundness/preservation projections.

#### Statement
`Theorem internal_call_no_type_error` in `vyperTypeCallSoundnessScript.sml`.

#### Approach
Use `fn_sig_argument_bounds`, `internal_call_signature_sound`, and `functions_well_typed_body` to obtain body typing and parameter/default facts. Evaluate arguments/defaults with expression/default soundness. Invoke the statement/body no-TypeError theorem for the function body and propagate through call-return wrapper code.

#### Not to try
Do not reconstruct `functions_well_typed` internals manually in the large proof if `functions_well_typed_body` applies. Do not weaken the theorem to omit `functions_well_typed cx`.

### C5.3: Internal call success preservation wrapper
- Kind: `proof`
- Risk: 2
- Work priority: 20
- Work units: 8
- Rationale: It reuses the internal-call decomposition and projects the success state/value typing facts.
- Dependencies: C5.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C5.3

#### Progress note
Completes the task-listed internal call wrapper pair.

#### Summary
Prove `internal_call_type_preservation`. On successful internal call evaluation, show the final state remains well typed and the returned value is `expr_runtime_typed` for the call expression.

#### Statement
`Theorem internal_call_type_preservation` in `vyperTypeCallSoundnessScript.sml`.

#### Approach
Follow the same evaluator decomposition as C5.2, but retain the final success equation. Use statement body preservation/return typing to prove returned value type and state/accounts invariants. Then simplify `expr_runtime_typed` for the call expression using the signature return type equality from static typing.

#### Not to try
Do not prove this independently from C5.2 by a separate large case split; factor or reuse the same helper decomposition where possible.

### C6: Public fresh soundness wrapper surface
- Kind: `proof_group`
- Risk: 2
- Work priority: 60
- Work units: 0
- Rationale: The frozen public behaviors are projections of the subsystem joint invariants once assignment/statement/call/builtin layers are cheat-free.
- Required for completion: yes
- Dependencies: C1, C2, C3, C4, C5
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C6

#### Progress note
Preserves public theorem names/equivalent strength while allowing internal helper statements to have changed.

#### Summary
Ensure `vyperTypeSoundnessNewScript.sml` exposes wrappers equivalent in strength to the six frozen public obligations. Prove/repair only wrapper projections; missing facts should be exported from subsystem layers, not reproved here.

#### Approach
Prove each wrapper by applying the relevant subsystem theorem and simplifying the result projection. Keep theorem names and strength equivalent to the task list. After wrappers, build the aggregator to ensure all dependencies are reachable and clean.

#### Not to try
Do not copy old retired proof scripts wholesale. Do not change frozen public behavior to match an easier internal theorem.

#### Argument
The final fresh surface has no new semantic induction. Statement and expression no-TypeError wrappers project the `no_type_error_result` conjuncts. Success preservation wrappers project state/env/accounts/result typing from statement/expression joint soundness. Exception preservation projects the return-exception typing and state invariants. Callable-body no-TypeError composes call-entry/function-body soundness with statement soundness.

#### Definition design
The public interface should hide strengthened internal side conditions by deriving them from public well-typedness/context hypotheses. If a public wrapper cannot be proved, that indicates a missing subsystem corollary or an underspecified public hypothesis; because public behavior is frozen, add/export the missing internal corollary rather than weakening public behavior.

#### Code structure
Wrapper edits belong only in `semantics/prop/vyperTypeSoundnessNewScript.sml` and, if absolutely necessary, small projection corollaries in subsystem files. Do not import retired old soundness theories unless C0 proves they are still in the fresh dependency chain.

### C6.1: Prove/repair the six public wrapper theorems
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 8
- Rationale: Wrapper projection is standard after subsystem theorems are complete; any failure is evidence of a missing projection lemma, not new architecture.
- Dependencies: C5.3, C2.3, C1.6
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C6.1

#### Progress note
Same public wrapper obligation as pre-collapse plan.

#### Summary
Close wrappers equivalent to `typed_stmts_no_type_error`, `typed_stmts_success_preserves_state_env`, `typed_stmts_exception_preserves_state_and_return_type`, `typed_expr_no_type_error`, `typed_expr_success_preserves_type`, and `typed_callable_body_no_type_error`.

#### Statement
Current-source public wrapper theorems in `semantics/prop/vyperTypeSoundnessNewScript.sml`, equivalent in strength to the six names listed in the TASK file.

#### Approach
For each wrapper, instantiate the strongest available subsystem theorem and destruct only the final conjunction/case result needed. If the subsystem theorem statement changed, add a compatibility corollary with the public wrapper name/strength. Keep all public hypotheses derivable from the source typing/context assumptions.

#### Not to try
Do not weaken public theorem conclusions or add visible public preconditions without user approval; these behaviors are frozen by the TASK.

### C7: Final `vyperSemanticsHolTheory` zero-CHEAT validation
- Kind: `validation`
- Risk: 1
- Work priority: 70
- Work units: 2
- Rationale: Mechanical final build/audit; any remaining warning is concrete evidence for a small follow-up replan.
- Required for completion: yes
- Dependencies: C6.1
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: pre-collapse C7

#### Progress note
Final validation component is carried forward unchanged in purpose.

#### Summary
Run `holbuild build vyperSemanticsHolTheory` and confirm success with zero CHEAT warnings reachable from the theory. If any warning remains, report the exact theorem/file and request a scoped replan rather than declaring completion.

#### Description
This is the task done-definition check. It must be performed after all proof components, because HOL can build through cheated theorems while still emitting warnings.

#### Statement
Command-level obligation: `holbuild build vyperSemanticsHolTheory` succeeds with zero reachable CHEAT warnings.

#### Approach
Use holbuild only. Capture the full warning summary and, if clean, close the task. If not clean, map each remaining warning to an existing component if possible; if it is uncovered, escalate PLAN_INCOMPLETE with the exact warning list.

#### Not to try
Do not ignore CHEAT warnings because the build exit code is zero. Do not clean unrelated warnings outside the dependency cone unless they are reachable from `vyperSemanticsHolTheory`.
