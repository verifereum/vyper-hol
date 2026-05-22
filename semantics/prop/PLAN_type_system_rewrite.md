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

### C2: Statement/type soundness fresh-stack obligations
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C2.1.1.13.3 risk 3. The planned inline ordinary Expr_Subscript proof is forcing brittle proof plumbing before reaching the branch-specific tail lemmas. After applying the base IH, exact `qpat_x_assum` selection fails for the visible ordinary implication; stack-based projection can expose it but then discharging/simplifying the implication either times out or DISCH_THEN/first_x_assum matching fails. Splitting the base result by the renamed `base_res` fails because HOL does not see it as a free variable in the goal, while splitting `FST (eval_expr cx e st)` creates 8 branchy goals without substituting the evaluator equality. Attempts to abbreviate the visible `case (base_res,st1)` tail did not bind a case-splittable variable. This indicates the active leaf needs a better boundary helper or revised proof interface rather than more inline tactics.
- Required for completion: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2 plan

#### Progress note
Ancestor carried forward unchanged; included only because the PLAN update introduces dotted descendants below C2.1.1.13.2.

#### Summary
- Ancestor context for the statement-soundness subtree.
- No strategy change is made at this level.
- The only new work is the local Expr_Subscript build-gate repair below C2.1.1.13.2.

#### Argument
The broader statement-soundness proof continues to follow the existing joint evaluator invariant and case-by-case Resume structure. This update does not change any statement-level semantic invariant.

#### Definition design
No definition interface changes are authorized at this ancestor level. The update only adds a proof-performance boundary needed for reliable holbuild before the Subscript helper.

#### Code structure
Keep work in `semantics/prop/vyperTypeStmtSoundnessScript.sml`; no file split or library extraction is introduced by this update.

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

### C2.1: Evaluator statement soundness mutual proof repairs
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C2.1.1.13.3 risk 3. The planned inline ordinary Expr_Subscript proof is forcing brittle proof plumbing before reaching the branch-specific tail lemmas. After applying the base IH, exact `qpat_x_assum` selection fails for the visible ordinary implication; stack-based projection can expose it but then discharging/simplifying the implication either times out or DISCH_THEN/first_x_assum matching fails. Splitting the base result by the renamed `base_res` fails because HOL does not see it as a free variable in the goal, while splitting `FST (eval_expr cx e st)` creates 8 branchy goals without substituting the evaluator equality. Attempts to abbreviate the visible `case (base_res,st1)` tail did not bind a case-splittable variable. This indicates the active leaf needs a better boundary helper or revised proof interface rather than more inline tactics.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.1 plan

#### Progress note
No prior progress under C2.1 is invalidated. This ancestor is included only to provide explicit parentage for the C2.1.1.13.2 replacement.

#### Summary
- Ancestor for evaluator mutual-proof case repairs.
- Existing joint-invariant strategy remains unchanged.
- The update only authorizes a local proof refactor and the original Subscript helper proof.

#### Argument
The evaluator mutual proof should continue to avoid duplicate inductions and prove the all-result joint invariant through local case lemmas. The IfExp timeout repair is purely a robustification of an already-local helper proof.

#### Definition design
No new definitions or theorem statements are introduced at this ancestor beyond the planned Subscript projection helper in the child. Failure signs remain broad simplification over mutual-IH contexts.

#### Code structure
All edits remain local to `vyperTypeStmtSoundnessScript.sml`. Do not move IfExp or Subscript helpers between theories for this update.

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

### C2.1.1: Expression cases in eval_all_type_sound_mutual
- Kind: `proof`
- Risk: 3
- Work priority: 0
- Work units: 0
- Rationale: Derived from child component C2.1.1.13.3 risk 3. The planned inline ordinary Expr_Subscript proof is forcing brittle proof plumbing before reaching the branch-specific tail lemmas. After applying the base IH, exact `qpat_x_assum` selection fails for the visible ordinary implication; stack-based projection can expose it but then discharging/simplifying the implication either times out or DISCH_THEN/first_x_assum matching fails. Splitting the base result by the renamed `base_res` fails because HOL does not see it as a free variable in the goal, while splitting `FST (eval_expr cx e st)` creates 8 branchy goals without substituting the evaluator equality. Attempts to abbreviate the visible `case (base_res,st1)` tail did not bind a case-splittable variable. This indicates the active leaf needs a better boundary helper or revised proof interface rather than more inline tactics.
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.1.1 plan

#### Progress note
No expression-case strategy is replaced. The update adds a prerequisite child under the active Subscript component to keep cold holbuild reliable.

#### Summary
- Ancestor for expression evaluator cases.
- The IfExp proof-performance issue is a prerequisite build gate, not a new semantic case obligation.
- Expr_Subscript remains decomposed into cleanup, projection helper, ordinary half, and place-projection half.

#### Argument
Expression cases are discharged by preserving branch-specific static facts until they match evaluator-tail boundary lemmas. Broad rewrites over the mutual proof context are avoided because they lose structure and can time out.

#### Definition design
Boundary lemmas should expose exactly the facts needed by each expression case: ordinary expression results use `expr_result_typed`, while place/projection branches use `place_expr_result_typed`. The IfExp repair must not introduce a new interface.

#### Code structure
Keep local helper theorems near their consumer cases in `vyperTypeStmtSoundnessScript.sml`. The IfExp refactor is an in-place proof edit around `ifexp_branch_from_cond_ih`; the Subscript helper remains immediately before the Expr_Subscript Resume.

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

### C2.1.1.13: Repair Expr_Subscript by static-disjunct split and exact place-tail helper
- Kind: `proof_refactor`
- Risk: 3
- Work priority: 13
- Work units: 0
- Rationale: Derived from child component C2.1.1.13.3 risk 3. The planned inline ordinary Expr_Subscript proof is forcing brittle proof plumbing before reaching the branch-specific tail lemmas. After applying the base IH, exact `qpat_x_assum` selection fails for the visible ordinary implication; stack-based projection can expose it but then discharging/simplifying the implication either times out or DISCH_THEN/first_x_assum matching fails. Splitting the base result by the renamed `base_res` fails because HOL does not see it as a free variable in the goal, while splitting `FST (eval_expr cx e st)` creates 8 branchy goals without substituting the evaluator equality. Attempts to abbreviate the visible `case (base_res,st1)` tail did not bind a case-splittable variable. This indicates the active leaf needs a better boundary helper or revised proof interface rather than more inline tactics.
- Supersedes: C2.1.1.13 previous tactical subtree, C2.1.1.13.2.1, C2.1.1.13.2.2
- Progress transition: `refinement`
- Carries progress/evidence from: E0678, existing C2.1.1.13 strategy, C2.1.1.13.1 completed cleanup
- Invalidates prior progress/evidence: old tactical children C2.1.1.13.2.1, old tactical child C2.1.1.13.2.2 as a standalone child

#### Progress note
This replacement rebases the Expr_Subscript subtree after repeated tactical augmentations. The accepted cleanup remains valid; the two tactical children under C2.1.1.13.2 are collapsed into one beginable leaf so the executor can make the minimal IfExp performance edit and prove the Subscript projection helper in the same local build episode.

#### Summary
- Rebase and flatten the active Expr_Subscript repair subtree.
- Keep the accepted normalization cleanup as carried-forward evidence.
- Collapse the IfExp timeout refactor and Subscript projection helper into one beginable boundary-lemma leaf.
- Preserve the planned order: cleanup evidence, helper/build gate, ordinary Subscript half, place-projection Subscript half.
- Do not broaden to Expr_Attribute, assignment cases, or builtin/call obligations in this subtree.

#### Description
This parent replaces the over-decomposed local subtree and is not itself a beginable work item. It authorizes exactly the local proof infrastructure needed to continue the Expr_Subscript case after checkpoint invalidation exposed an earlier proof-performance problem.

#### Approach
Use this subtree only to complete the Subscript-local proof architecture. The executor should begin leaves, not this parent. If the combined helper/build-gate leaf still needs additional semantic facts, escalate with the exact helper subgoal rather than adding tactical descendants.

#### Not to try
Do not add further descendants under C2.1.1.13.2 for individual tactic steps. Do not reintroduce the old shared `FIRST [irule expr_subscript_place_tail_sound_stmt; ...]` success tail, because it loses the active static disjunct. Do not use global `gvs[well_typed_expr_def,type_place_expr_def,AllCaseEqs()]` over the full mutual Resume context.

#### Argument
Expr_Subscript must be proved by preserving the static disjunction between ordinary expression typing and place/projection typing until the evaluator tail is discharged. The ordinary successful result can use `expr_result_typed`; the place/projection successful result must use `place_expr_result_typed`, especially for nested storage/hashmap references where ordinary expression typing is the wrong interface. The earlier `ifexp_branch_from_cond_ih` timeout is not a semantic dependency of Subscript, but cold `holbuild` must pass it before the local helper can be validated, so it is included in the same shallow build-gate leaf rather than as another durable semantic child. Once the projection-tail helper is proved, the two Resume halves should only wire branch facts and exact evaluator-tail equalities into the helper, avoiding repeated unfolding in consumers.

#### Definition design
The boundary interface to provide is `expr_subscript_place_projection_tail_sound_stmt`. It consumes the base place typing fact `type_place_expr env e = SOME base_vt`, the projection fact `subscript_vtype base_vt (expr_type e') = SOME result_vt`, annotation compatibility `vtype_annotation_ok result_vt v9`, base/index runtime typing facts, successful `get_Value`, and the exact monadic evaluator-tail equality. It returns state/env/account preservation, `no_type_error_result`, and on successful result `place_expr_result_typed env tv result_vt`. This helper intentionally hides `evaluate_subscript_def`, `check_array_bounds`, storage-read cases, and nested HashMap/place cases from the mutual Resume proof. Failure signs are broad simplification over the whole mutual context, quoted copies of the monadic tail, or attempts to replace `place_expr_result_typed` with `expr_result_typed`.

#### Code structure
All edits stay in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. First make the local proof of `ifexp_branch_from_cond_ih` rebuild robust in place near lines 6228-6263 by replacing the initial broad `rw[]` with controlled introduction/simplification. Then prove `expr_subscript_place_projection_tail_sound_stmt` immediately after `expr_subscript_place_tail_sound_stmt` and before the `Expr_Subscript` Resume. Keep evaluator-tail case analysis inside this helper. Leave the normalized `Expr_Subscript` placeholder for later leaves; do not edit Expr_Attribute or later cases here.

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

### C2.1.1.13.4: Close the separate Subscript place-projection half
- Kind: `proof`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: The new projection helper gives the exact successful-result conclusion required by the reverse/place conjunct; remaining work is standard IH and evaluator-tail wiring.
- Dependencies: C2.1.1.13.2, C2.1.1.13.3
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: existing C2.1.1.13.4 plan

#### Progress note
This leaf is carried forward from the previous subtree, now depending on the flattened helper/build-gate leaf. It should complete the Expr_Subscript Resume and remove its placeholder cheat.

#### Summary
- Fill the reverse/place-projection conjunct of `eval_all_type_sound_mutual[Expr_Subscript]`.
- Use `expr_subscript_place_projection_tail_sound_stmt` as the main boundary lemma.
- Successful Subscript place projections must conclude `place_expr_result_typed env tv result_vt`.
- Completing this leaf should remove the `Expr_Subscript` placeholder cheat and build `vyperTypeStmtSoundnessTheory`.

#### Description
This is the semantic consumer of the projection-tail helper. It should be small if C2.1.1.13.2 exposed the right interface: the mutual proof supplies base expression/place IH results, index expression IH results, `get_Value`, and the exact evaluator-tail equality; the helper supplies preservation/no-TypeError/place-typed success.

#### Statement
No separate theorem statement. Target is the remaining place/projection conjunct inside:

```sml
Resume eval_all_type_sound_mutual[Expr_Subscript]: ...
```

The completed Resume should no longer contain the normalized `cheat` placeholder for `Expr_Subscript`.

#### Approach
Use the same evaluator-case skeleton as the ordinary half, but when the static fact is `type_place_expr env e = SOME base_vt` and `subscript_vtype base_vt (expr_type e') = SOME result_vt`, route the tail to `expr_subscript_place_projection_tail_sound_stmt`. Instantiate it from branch facts rather than unfolding `evaluate_subscript_def` in the Resume. Then discharge successful result typing by the helper's `place_expr_result_typed` conclusion and preserve state/env/account/no-TypeError facts directly.

#### Not to try
Do not unfold the full Subscript evaluator tail in the mutual Resume after the helper exists. Do not coerce the helper result into `expr_result_typed`; the reverse conjunct requires place typing. Do not edit assignment, builtin, call, or Expr_Attribute obligations as part of this leaf.

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
