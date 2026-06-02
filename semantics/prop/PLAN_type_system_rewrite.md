# PLAN

## Structured Components

### C0: Type-system rewrite proof completion gate context
- Kind: `proof_group`
- Risk: 4
- Work priority: 0
- Work units: 0
- Rationale: Carries the existing high-risk status because descendant `C0.2.3.2.2.2` remains blocked; this augment does not redesign the top-level proof.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0

#### Progress note
Included only as an explicit dotted parent required by the PLAN output schema; not a redesign.

#### Summary
Schema parent for the scoped update. No new top-level work is authorized here. Risk is inherited from the blocked ExtCall static driver-tail descendant.

#### Argument
No new top-level argument is supplied by this scoped augment. The only substantive update is the descendant stop/report gate for the static ExtCall optional-driver IH boundary.

#### Definition design
No definitions are changed. Evaluator/semantics definitions remain off-limits; proof-interface trouble is localized to the generated mutual IH boundary.

#### Code structure
No file-organization change is authorized in this scoped augment. Any broader proof-architecture refactor would require a separate ancestor-level replacement.

### C0.1: Refactor static ExtCall Resume into a branch-local suspended success continuation
- Kind: `proof_architecture_probe`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Already completed by E0156. It remains the structural basis for the current static ExtCall proof shape and imposes no remaining executor work.
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1, E0156

#### Progress note
Carry forward completed checkpoint evidence; no new scheduling work is intended.

#### Summary
Completed checkpoint. Static ExtCall prefix/error branch structure was isolated enough to make the success continuation the active focus. Keep the resulting source structure unless a build failure specifically implicates it.

#### Approach
No action unless the source unexpectedly no longer builds before the active static-success Resume. If audited, preserve the branch-local suspension/refactor shape and do not restart older prefix-replay strategies.

#### Not to try
Do not reopen the old broad linear proof attempt that timed out before the maintainer clarification and C0.2 replacement.

### C0.2: ExtCall/RawCall proof context
- Kind: `proof_group`
- Risk: 4
- Work priority: 0
- Work units: 0
- Rationale: Carries inherited risk from the unresolved static ExtCall driver-tail IH boundary.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2

#### Progress note
Included only as an explicit dotted parent required by the PLAN output schema; omitted descendants remain preserved.

#### Summary
Schema parent for the scoped ExtCall stop-gate update. No sibling work is added. Risk remains inherited from `C0.2.3.2.2.2`.

#### Argument
No new subtree argument is introduced here. The relevant invariant remains that ExtCall proof branches must expose the recursive optional-driver soundness premise only after legal branch isolation.

#### Definition design
No evaluator or semantics definition changes. The failing interface is the generated induction hypothesis shape, not a runtime definition counterexample.

#### Code structure
No edits outside `semantics/prop`; no source movement is authorized by this augment.

### C0.2.1: Carry forward proved static ExtCall projected-soundness helper
- Kind: `boundary_lemma`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0159 proved the helper and E0161 did not undermine its truth. It may or may not be the final helper used by the repaired Resume proof, but the source progress is valid and should not be redone.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.1, E0159, TO_type_system_rewrite-20260601T220715Z_m3320_t001, TO_type_system_rewrite-20260601T220715Z_m3326_t001

#### Progress note
This component is retained as completed source progress under the replaced C0.2 subtree.

#### Summary
- Already proved and committed as part of C0.2 progress.
- Keep the theorem in the source; do not rework it unless it blocks the repaired proof.
- It documents the ordinary-evaluator boundary for static ExtCall and may still be useful as a reference.
- No executor work remains for this leaf.

#### Approach
Audit only if a build unexpectedly fails before the active Resume. Otherwise carry forward this proof unchanged.

#### Not to try
Do not revert the targeted `rewrite_tac[Once well_typed_expr_def]` performance fix in `extcall_expr_sound_from_generated_ih`; prior evidence shows broad `simp` timed out after adding helpers.

### C0.2.2: Add or expose a tiny option-typing helper for `THE drv` if needed
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: This is a mechanical option case split and prevents the static Resume proof from unfolding expression typing in a very large context. It is the first real executable leaf after the frontier repair.
- Dependencies: C0.1
- Progress transition: `refinement`
- Carries progress/evidence from: E0161

#### Progress note
This is the same intended tiny helper from the replaced C0.2 plan, now made the first executable C0.2 leaf by removing the completed C0.2.1 evidence leaf.

#### Summary
- Next beginable component after this repair.
- Reuse an existing option-typing theorem if visible; otherwise prove a local theorem.
- Desired fact: `well_typed_opt env drv /\ IS_SOME drv ==> well_typed_expr env (THE drv)`.
- The helper must not mention ExtCall prefix facts.
- If not needed, record that the existing source/imported fact suffices and move to C0.2.3.

#### Statement
Theorem well_typed_opt_THE[local]:
  well_typed_opt env drv /\ IS_SOME drv ==> well_typed_expr env (THE drv)

#### Approach
Search locally/imports for `well_typed_opt_THE` or `well_typed_opt_SOME`. If absent, prove by `Cases_on drv`; `NONE` contradicts `IS_SOME`, and `SOME e` follows by unfolding only the option typing definition or small option theorem. Do not unfold `well_typed_expr_def` in the large static Resume context.

#### Not to try
Do not edit outside `semantics/prop`. Do not solve this by broad simplification inside `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`.

### C0.2.3: ExtCall static proof context
- Kind: `proof_group`
- Risk: 4
- Work priority: 0
- Work units: 0
- Rationale: Carries inherited risk from the unresolved static driver-tail compact-IH producer.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.3

#### Progress note
Included only as an explicit dotted parent required by the PLAN output schema.

#### Summary
Schema parent for the scoped static ExtCall driver-tail blocker. No additional proof components are authorized. Risk remains inherited.

#### Argument
The static ExtCall proof has already been narrowed to a concrete success continuation; the unresolved issue is obtaining a usable driver IH without replaying the full generated prefix.

#### Definition design
The proof-interface boundary should expose a compact conditional driver IH. Current local boundary exposes only the generated full-prefix IH.

#### Code structure
No local file refactor is planned here. A real repair would likely move/refactor a suspend/Resume boundary, which is outside this scoped augment.

### C0.2.3.1: Carry forward the static Resume prefix probe to the concrete success-tail branch
- Kind: `proof_probe`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: Already completed in E0166 and not invalidated by E0167.
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: E0166

#### Progress note
The E0167 final conversion failure does not undermine the prefix checkpoint.

#### Summary
- Carry forward the completed static ExtCall success prefix probe.
- It shows the proof reaches `run_ext_call ... = SOME (T,q',q'',r)`.
- It identifies the tail state as `args_st with <|accounts := q''; tStorage := r|>`.
- No new executor work is required unless source drift breaks replay.

#### Description
This is the stable prefix-shape checkpoint for the replacement subtree.

#### Approach
Reuse the checked E0166 linear monadic splitting skeleton. If replay unexpectedly fails, restore that style rather than broad case cleanup.

#### Not to try
Do not expand this probe into the full proof; it only certifies the prefix/tail shape.

### C0.2.3.2: Static ExtCall success-branch context
- Kind: `proof_group`
- Risk: 4
- Work priority: 0
- Work units: 0
- Rationale: Carries inherited risk from the concrete driver-tail branch where compact optional-driver IH production is blocked.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2.3.2

#### Progress note
Included only as an explicit dotted parent required by the PLAN output schema.

#### Summary
Schema parent for the isolated static-success branch blocker. The branch isolation progress is preserved. No new local tactic work is authorized.

#### Argument
The branch-by-branch approach remains valid up to the point where `run_ext_call` succeeds and updates accounts/transient storage. The remaining driver continuation should be discharged by the existing after-update helper, but only if a compact recursive IH is available.

#### Definition design
The desired boundary lemma interface is `extcall_after_state_update_tail_sound_cond_driver_ih`; it expects a small conditional driver-IH premise. The generated mutual IH does not currently provide that premise natively at this Resume boundary.

#### Code structure
All relevant code remains in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. No broader proof-architecture edit is authorized in this scoped update.

### C0.2.3.2.1: Insert a focused static-driver-tail suspension at the already split branch
- Kind: `proof_refactor`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: This is a small, reversible source-structure edit at the existing marker. It does not prove the theorem or change definitions; it only tests whether the proof architecture can expose the driver branch as a focused obligation under the clarified rules.
- Checkpoint: yes
- Supersedes: C0.2.3.2.1@old, C0.2.3.2.3
- Progress transition: `refinement`
- Carries progress/evidence from: E0175, E0177, E0180, TO_type_system_rewrite-20260601T220715Z_m3592_t001

#### Progress note
Prior evidence that the script reaches the marker remains valid. This component turns that marker into an empirical focused proof boundary rather than treating it as terminal blocked status.

#### Summary
- Work in `semantics/prop/vyperTypeStmtSoundnessScript.sml` at `FAIL_TAC "c0_2_3_2_2_1_driver_branch_remaining"`.
- Keep all existing linear prefix splitting and closed error/non-driver cases.
- Replace the marker with a focused suspension for the true driver branch, using a clear name such as `Expr_Call_ExtCall_static_driver_tail`.
- Build/check enough to confirm the focused obligation is generated and the surrounding static-success Resume remains well-formed.
- Stop and report if inserting the suspension disrupts already accepted prefix progress.

#### Description
The purpose is to rebase the proof boundary to the point allowed by the maintainer clarification: after the ExtCall prefix has been split and discharged, in the single success-continuation branch. This component should not add a cheat, change semantics, or attempt large proof search. It should leave the file in a state where the next Resume obligation is exactly the branch that currently reaches the marker.

#### Statement
Focused proof-boundary target in `vyperTypeStmtSoundnessScript.sml`:

```sml
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]
```

should no longer end in

```sml
FAIL_TAC "c0_2_3_2_2_1_driver_branch_remaining"
```

but should suspend the already focused remaining branch, e.g.

```sml
suspend "Expr_Call_ExtCall_static_driver_tail"
```

at that point.

#### Approach
Make the smallest possible edit: after the existing `Cases_on `q' = [] /\ IS_SOME drv` >> gvs[]` and the attempted non-driver closure, replace the final marker by a named suspension for the remaining branch. Run the local build/check command normally used for Resume obligations to ensure the suspension is accepted. Record the exact focused assumptions if the build output prints them.

#### Not to try
Do not rearrange the whole ExtCall proof prefix. Do not add a theorem adapter for the generated prefix. Do not start proving the focused branch in this component unless it is literally immediate after the suspension edit; the next component owns that proof.

### C0.2.3.2.2: Static ExtCall after-update tail: stabilize and stop/report proof-interface blocker
- Kind: `stop_gate_group`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The executable work in this replacement is low-risk administrative/stabilization work: preserve the accepted branch-isolation evidence, restore the source to a stable intentional-cheat baseline if it is still at the diagnostic marker, update the in-scope plan/state notes, and report that no legal straightforward proof route remains. This does not claim the ExtCall proof obligation is solved; it prevents more forbidden local generated-IH proof search.
- Progress transition: `replacement`
- Carries progress/evidence from: C0.2.3.2.2, E0199, E0200, TO_type_system_rewrite-20260601T220715Z_m3864_t001, TO_type_system_rewrite-20260601T220715Z_m3879_t001, TO_type_system_rewrite-20260601T220715Z_m3882_t001
- Invalidates prior progress/evidence: C0.2.3.2.2.2, C0.2.3.2.2.2.2, C0.2.3.2.2.3

#### Progress note
Replaces the earlier proof-producing subtree. E0199 remains useful evidence that the exact static driver-success branch can be isolated. E0200 invalidates the planned compact-IH producer and any downstream consumer assuming `static_driver_ih` exists.

#### Summary
- Accepted fact: the static ExtCall driver-success branch can be reached with concrete run/update facts and labelled `generated_driver_ih`.
- Blocking fact: deriving a compact branch-local optional-driver IH from `generated_driver_ih` is not straightforward and prior legal attempts failed.
- Do not add more local tactic children under the old producer; this is a proof-interface problem.
- Immediate work is to restore/stabilize source if needed, record the stop in `semantics/prop` plan/state files, and stop/report.
- The ExtCall theorem remains intentionally unresolved until maintainer direction authorizes a broader proof-architecture replacement.

#### Description
This subtree no longer tries to prove `Expr_Call_ExtCall_static_driver_tail`. The current evidence demonstrates that the source proof can isolate the desired concrete branch, but the mutual induction interface supplies only a generated-prefix-guarded IH. Converting that IH locally would require either broad generated-prefix simplification, many-variable generated-prefix plumbing, or a generated-prefix adapter theorem; those routes are forbidden by the maintainer clarification and/or already timed out. The correct task-scoped response is to leave the repository stable and report the proof-interface blocker, not to continue proof search.

#### Statement
Administrative replacement for the blocked proof subtree around `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_driver_tail]` in `semantics/prop/vyperTypeStmtSoundnessScript.sml`. No new theorem statement is authorized here.

#### Approach
First preserve the useful E0199 information in comments/plan notes only; do not rely on the diagnostic `FAIL_TAC` as a buildable state. If the source still contains `FAIL_TAC "c0_2_3_2_2_2_1_isolated_static_driver_success"`, replace that partial Resume body with the stable intentional cheated baseline for the ExtCall static driver tail (or the smallest local `cheat` at that Resume) so `vyperTypeStmtSoundnessTheory` can build with the known reachable cheat. Then update `TYPE_SYSTEM_REWRITE_PLAN.md`/`STATE_type_system_rewrite.md` to say this subtree stopped because compact optional-driver IH production is a proof-interface blocker.

#### Not to try
Do not try `asm "generated_driver_ih" irule`, `drule_then`/`qspecl_then` over a hand-built generated-prefix conjunction, `mp_tac >> simp[]` over the generated IH, broad `gvs`/`AllCaseEqs()` cleanup, or a generated-prefix adapter theorem. Those have failed or violate the maintainer clarification. Do not begin downstream static/nonstatic ExtCall or RawCallTarget consumers while `static_driver_ih` is absent.

#### Argument
The mathematical soundness route would need the optional driver expression to inherit the mutual expression soundness postcondition at the post-external-call state. In the current generated induction proof, that postcondition is guarded by the entire preceding ExtCall monadic prefix. E0199 shows the prefix facts are concretely true in the static success branch; E0200 shows that turning them into a usable compact local IH is not a straightforward proof step under the allowed tactics. Therefore the only sound local action is to stop and preserve evidence; proving the theorem now requires an ancestor-level proof-boundary redesign that exposes the driver IH natively, which is outside this replacement unless new maintainer direction is supplied.

#### Definition design
No evaluator/type-system definition change is allowed. No new semantic helper definition should be introduced to encode the generated prefix. In particular, do not define an ExtCall-prefix predicate just to feed `generated_driver_ih`; that is the forbidden adapter architecture under another name. Any future proof-architecture redesign should move the suspend/proof boundary or mutual proof structure so the optional-driver IH is produced as a native branch-local assumption, not reconstructed locally.

#### Code structure
All edits stay under `semantics/prop`. `vyperTypeStmtSoundnessScript.sml` should be restored to a buildable intentional-cheat baseline at the blocked ExtCall Resume if it currently contains a diagnostic `FAIL_TAC` marker. `TYPE_SYSTEM_REWRITE_PLAN.md` and `STATE_type_system_rewrite.md` should record the accepted branch-isolation evidence and the stop condition. Do not edit evaluator/semantics definitions or files outside `semantics/prop`.

### C0.2.3.2.2.1: Restore the static-driver-tail Resume to a stable intentional-cheat baseline
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 1
- Rationale: This is a mechanical stabilization step if the source still contains the accepted diagnostic marker. It removes a non-buildable marker and restores the known intentional cheated baseline without changing semantics or theorem statements.
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: E0199, TO_type_system_rewrite-20260601T220715Z_m3857_t001, TO_type_system_rewrite-20260601T220715Z_m3884_t001

#### Progress note
Carries forward the fact that the marker was useful diagnostic evidence, but the marker should not remain as the stable source state once the task is stopped.

#### Summary
- Inspect `semantics/prop/vyperTypeStmtSoundnessScript.sml` at `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_driver_tail]`.
- If the body ends at `FAIL_TAC "c0_2_3_2_2_2_1_isolated_static_driver_success"`, replace that diagnostic partial proof with the stable local `cheat` for this Resume.
- Do not modify evaluator definitions or any file outside `semantics/prop`.
- Verify only that `holbuild build vyperTypeStmtSoundnessTheory` reaches the known cheated baseline, not that ExtCall is proved.

#### Description
The accepted marker is evidence, but it intentionally fails holbuild. Since the proof-interface blocker is being reported rather than solved, the repository should not be left in a marker-failing state. Restore the smallest local cheat at `Expr_Call_ExtCall_static_driver_tail`/the corresponding ExtCall static tail location so the fresh-stack build is stable with the known reachable cheat inventory.

#### Statement
Source stabilization obligation: `vyperTypeStmtSoundnessTheory` should build again with an intentional ExtCall cheat rather than fail at `c0_2_3_2_2_2_1_isolated_static_driver_success`.

#### Approach
Make the minimal edit in `vyperTypeStmtSoundnessScript.sml`: replace the diagnostic branch-isolation proof body/marker with `cheat` at the suspended Resume, preserving surrounding theorem names and existing suspend structure. Then run `holbuild build vyperTypeStmtSoundnessTheory` with the normal timeout. The expected result is a successful build with CHEAT warning(s), not a zero-cheat build.

#### Not to try
Do not continue from the marker toward `static_driver_ih`. Do not delete the ExtCall theorem or change its statement. Do not attempt to make the whole `vyperSemanticsHolTheory` zero-cheat as part of this cleanup.

### C0.2.3.2.2.2: Record the ExtCall generated-IH proof-interface blocker in in-scope plan/state files
- Kind: `plan_update`
- Risk: 1
- Work priority: 1
- Work units: 1
- Rationale: Updating the in-scope documentation is mechanical and required by the task's instruction to update the plan as progress/issues are found.
- Dependencies: C0.2.3.2.2.1
- Progress transition: `replacement`
- Carries progress/evidence from: E0200, TO_type_system_rewrite-20260601T220715Z_m3864_t001, TO_type_system_rewrite-20260601T220715Z_m3879_t001, TO_type_system_rewrite-20260601T220715Z_m3882_t001
- Invalidates prior progress/evidence: C0.2.3.2.2.2.2, C0.2.3.2.2.3

#### Progress note
This replaces the obsolete plan that treated compact `static_driver_ih` production as Risk 2. It records that the producer is blocked and downstream consumers must not be scheduled.

#### Summary
- Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` to mark local static-driver-tail proof work stopped.
- Update `semantics/prop/STATE_type_system_rewrite.md` cursor/next_action to report the blocker rather than continue proof search.
- Mention E0199 as useful branch-isolation evidence and E0200 as the compact-IH failure.
- State that future progress requires maintainer-authorized ancestor-level proof-boundary redesign.

#### Description
The plan file currently contains historical ExtCall stop information plus later executable-plan notes. This component should make the current status unambiguous: local static driver-tail work has stopped because the generated optional-driver IH cannot be legally converted into the compact branch-local IH. Downstream ExtCall and RawCallTarget proof components remain blocked until a new maintainer-authorized architecture is provided.

#### Statement
Documentation obligation only: update in-scope plan/state files to reflect the accepted stop gate for `eval_all_type_sound_mutual[Expr_Call_ExtCall]`.

#### Approach
Add a short current-status subsection or replace the relevant stale scheduling text. Include the three negative evidence routes: direct `irule` no-match, explicit generated-prefix conjunction/forward chaining failure, and `mp_tac >> simp[]` timeout/forbidden route. Make clear that this is not theorem falsehood evidence; it is a proof-interface/design blocker under the task's straightforward-proof rule.

#### Not to try
Do not describe downstream components as ready while they depend on `static_driver_ih`. Do not erase the fact that branch isolation succeeded; that evidence may guide a future ancestor redesign. Do not promise a local helper theorem that reconstructs the generated prefix.

### C0.2.3.2.2.3: Stop/report: no legal local proof-producing frontier remains for static ExtCall driver tail
- Kind: `task_report`
- Risk: 2
- Work priority: 2
- Work units: 1
- Rationale: After stabilization and documentation, the remaining action is to report the blocker. The report is straightforward because the evidence is already checked and accepted; it does not require proof search.
- Dependencies: C0.2.3.2.2.1, C0.2.3.2.2.2
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: E0200, STATE_type_system_rewrite.md
- Invalidates prior progress/evidence: C0.2.3.2.2.2

#### Progress note
This terminal report supersedes the old blocked producer leaf. It confirms that no beginable local proof leaf should be created under this subtree without new maintainer direction.

#### Summary
- End this subtree by reporting a proof-interface blocker, not by proving ExtCall.
- The theorem is not shown false; the problem is the generated mutual IH shape.
- The local proof routes allowed by the maintainer clarification have been exhausted.
- Future work requires a broader proof-boundary redesign inside `semantics/prop`, authorized by maintainer direction.

#### Description
Once the source is stable and plan/state notes are updated, stop. The final message should say that `eval_all_type_sound_mutual[Expr_Call_ExtCall]` remains cheated/unfinished and that the current local static-driver-tail decomposition cannot legally produce the optional-driver IH. This satisfies the task instruction to stop on unexpected proof design issues.

#### Statement
Report obligation: local proof work on `Expr_Call_ExtCall_static_driver_tail` is blocked by generated optional-driver IH shape; no local Risk 1-2 proof frontier remains.

#### Approach
Prepare a concise report citing E0199 and E0200 evidence. State the exact forbidden/failing routes and the stable build status after cleanup. If a commit is made for cleanup/docs, use a non-GPG-signed commit as required by the task.

#### Not to try
Do not begin C0.2.3.2.3, C0.2.3.3, RawCallTarget, or final zero-cheat validation from this report. Do not ask the executor to keep searching locally after the report.

### C0.2.3.2.3: Integrate static ExtCall success only after the driver-IH gate is resolved
- Kind: `integration_build_audit`
- Risk: 2
- Work priority: 90
- Work units: 2
- Rationale: This component remains as the existing downstream dependency target, but it is not currently executable because it depends on the unresolved C0.2.3.2.2 gate. If a future plan supplies and proves a compact driver-IH architecture, this integration audit should be mechanical. Until then it must not be started.
- Dependencies: C0.2.3.2.2
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.3.2.3

#### Progress note
Preserved and clarified after the failed replacement attempt so external dependencies remain valid. Its dependency is intentionally kept on the unresolved gate, not on the terminal blocker child.

#### Summary
- Preserved to avoid dangling dependencies from C0.2.3.3 and C0.3.
- Its dependency is explicitly the unresolved driver-IH gate C0.2.3.2.2.
- It should only run after the static driver-tail Resume has a genuine proof, not after the terminal blocker report.
- If eventually authorized, check that the parent static-success Resume closes and `vyperTypeStmtSoundnessTheory` reaches the next intended obligation.
- Currently this is gated, not actionable.

#### Description
Do not use this component to bypass the static driver-tail proof. It is only an integration/build audit for a future successful proof architecture. In the current augmented plan, C0.2.3.2.2 remains a high-risk gate, so this component should not appear on the beginable frontier.

#### Statement
Integration audit for `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` and its focused `Expr_Call_ExtCall_static_driver_tail` subproof, once the driver-IH gate has been resolved by a new proof plan.

#### Approach
If this ever becomes executable after a future gate resolution, remove any temporary probe/failure marker from the focused Resume, verify that the full static success Resume closes, and run the task-specified build target within `semantics/prop`. Treat any reappearance of generated-prefix IH recovery as a regression and escalate rather than proving around it.

#### Not to try
Do not start this component while C0.2.3.2.2 is unresolved. Do not interpret the terminal blocker child C0.2.3.2.2.1 as satisfying this dependency. Do not run downstream components as a substitute for a static ExtCall success proof.

### C0.2.3.3: Deferred downstream static-success closure after focused rebase integration
- Kind: `main_proof`
- Risk: 2
- Work priority: 90
- Work units: 5
- Rationale: This is not the next executable leaf. It remains plausible standard proof work only after C0.2.3.2.3 has produced accepted build evidence for the focused static-driver-tail rebase. Before that dependency is complete, the component is stale/downstream and must remain unscheduled.
- Dependencies: C0.2.3.2.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.2.3.3, TO_type_system_rewrite-20260601T220715Z_m3595_t001

#### Progress note
Refined only to add the missing hard dependency on C0.2.3.2.3 and move the sibling priority after the static-success rebase subtree. Any prior proof idea for C0.2.3.3 is preserved, but it is not current frontier work until the rebase integration checkpoint is complete.

#### Summary
- Deferred downstream static-success closure; not beginable until C0.2.3.2.3 is done.
- Depends explicitly on the focused static-driver-tail proof and integration audit.
- Keeps the old boundary-helper direction only as downstream work after rebase evidence.
- If scheduled before C0.2.3.2.3, stop and report scheduler mismatch again.

#### Statement
Downstream closure of the relevant static-success Resume after the focused rebase has integrated build-cleanly. This component must not consume the old marker state directly; it depends on the theorem/script state produced by C0.2.3.2.3.

#### Approach
After C0.2.3.2.3 is accepted, use the integrated focused-tail result and existing projection/preservation boundary lemmas to finish any remaining static-success closure. Treat this as ordinary downstream proof work; do not reopen the generated-prefix recovery problem.

#### Not to try
Do not begin this component before C0.2.3.2.3. Do not use it as a workaround for proving C0.2.3.2.1 or C0.2.3.2.2. Do not recover driver premises from the top-level Resume context by broad simplification or generated-prefix adapters.

### C0.3: Close the nonstatic ExtCall result branch only after static ExtCall success rebase integration
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 80
- Work units: 5
- Rationale: E0186 shows C0.3 was scheduled prematurely because the structured dependency was too coarse. The proof obligation itself remains plausible standard downstream ExtCall work, but it must be gated behind the completed/reviewed static-success rebase checkpoint C0.2.3.2.3; before that it is not an executable frontier item.
- Dependencies: C0.2.3.2.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.3, E0186

#### Progress note
Carries forward the C0.3 proof obligation and accepts E0186 as scheduler-repair evidence only. No proof progress was made or invalidated in E0186; the component is refined by replacing the coarse dependency on C0.2.3 with the concrete terminal static-success rebase checkpoint C0.2.3.2.3.

#### Summary
- This is downstream nonstatic ExtCall result proof work, not the next proof action.
- Begin only after the focused static ExtCall success rebase has completed and been reviewed through C0.2.3.2.3.
- The intended next executable leaf remains C0.2.3.2.1, the focused static-driver-tail suspension insertion.
- Once unblocked, reuse the disciplined linear continuation interface validated by the static proof.
- Keep all edits under `semantics/prop` and do not change evaluator or semantics definitions.

#### Description
This component was incorrectly made beginable while the static ExtCall success branch was still intentionally staged through C0.2.3.2.1 -> C0.2.3.2.2 -> C0.2.3.2.3. E0186 validly closed C0.3 as stuck due to that dependency/scheduler artifact: no source edits or proof attempts were appropriate. The local repair is to make the concrete dependency match the component text and maintainer clarification, so nonstatic ExtCall work is deferred until the static-success branch-local IH interface has build-clean evidence.

#### Statement
Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  (* replace cheat using the validated ExtCall continuation interface, only after C0.2.3.2.3 *)

#### Approach
After C0.2.3.2.3 is accepted, reuse the successful static proof pattern: expose branch-local assumptions, split monadic operations linearly, close errors immediately, and use the relevant continuation/tail helper at the unique success tail. Treat any nonstatic-specific return-data or state-update facts as local to this Resume and stop if the branch is not analogous to the validated static proof.

#### Not to try
Do not start this before C0.2.3.2.3 is proved and reviewed. Do not recover driver/continuation premises from a broad top-level generated prefix by `simp`/`gvs`, `AllCaseEqs()`, or long generated-prefix adapter theorems. Do not use this component as permission to work on RawCallTarget, unrelated cheats, files outside `semantics/prop`, or evaluator/semantics definitions.

### C0.4: Prove RawCallTarget expression-call soundness through local tail boundaries
- Kind: `proof_subtree_parent`
- Risk: 2
- Work priority: 30
- Work units: 0
- Rationale: RawCallTarget work is standard local boundary proof work, but it must remain downstream of the ExtCall gates. Every executable RawCallTarget leaf now has a direct dependency path through C0.3 so it cannot appear on the frontier early.
- Dependencies: C0.3
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4

#### Progress note
This subtree is not strategically changed; only leaf dependencies are strengthened to repair frontier ordering.

#### Summary
- RawCallTarget is later work, not the current frontier.
- Begin only after static and nonstatic ExtCall result branches are complete.
- Prove small argument/return/tail boundary lemmas before replacing the RawCallTarget Resume.
- Keep all work inside `semantics/prop` and avoid evaluator definition changes.

#### Argument
RawCallTarget soundness should be packaged through local facts: destruct the runtime argument list, prove the flag-dependent returned value type, package the monadic tail's state/no-TypeError/result-typing facts, then replace the Resume using those boundaries. This avoids entangling RawCallTarget with the generated ExtCall optional-driver issue.

#### Definition design
No RawCallTarget semantic definition changes. Boundary lemmas should expose consumer-shaped facts: list/value destructors, flag-conditioned result typing, and a monadic tail soundness theorem. Failure sign: a Resume proof repeatedly unfolds the RawCallTarget tail internals instead of applying a boundary lemma.

#### Code structure
Place RawCallTarget boundary lemmas near analogous Send/RawLog/ExtCall helper blocks in `vyperTypeStmtSoundnessScript.sml`. Replace the RawCallTarget Resume only after all local boundary lemmas build.

### C0.4.1: Derive RawCallTarget runtime argument destructors
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 0
- Work units: 2
- Rationale: List-shape and value-typing inversion analogous to existing send/raw-log/ExtCall destructors. Direct dependency on C0.3 repairs the scheduler so this cannot begin before ExtCall gates.
- Dependencies: C0.3
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.1

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Prove the RawCallTarget runtime argument shape facts needed by the later tail proof. This is finite destructuring over evaluated arguments and their runtime typing. Begin only after C0.3.

#### Approach
Follow the nearby Send/RawLog argument inversion style. Keep conclusions consumer-shaped for C0.4.3; avoid proving a broad conjunction if separate destructors are easier to use.

#### Not to try
Do not begin before C0.3. Do not mix the monadic tail proof into the argument destructor lemma.

### C0.4.2: Prove flag-dependent RawCallTarget return value typing
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 10
- Work units: 2
- Rationale: Finite case analysis over RawCallTarget flags and return-shape definitions. Direct dependency on C0.3 blocks premature scheduling.
- Dependencies: C0.3
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.2

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Prove that the RawCallTarget result value has the type required by the return flag/shape. This is local finite case analysis and feeds the monadic tail boundary.

#### Approach
Case split on the relevant RawCallTarget mode/flags and simplify the return-value construction and type relation. State the theorem so C0.4.3 can apply it without unfolding the flag logic again.

#### Not to try
Do not combine this with state preservation or no-TypeError facts; keep it as a return-typing boundary.

### C0.4.3: Prove RawCallTarget monadic tail soundness boundary
- Kind: `boundary_lemma`
- Risk: 2
- Work priority: 20
- Work units: 5
- Rationale: Packages side-effect preservation, no-TypeError, and result typing for the already-split RawCallTarget tail. It depends on the argument and return boundaries and is downstream of C0.3.
- Dependencies: C0.4.1, C0.4.2
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.3

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Package the RawCallTarget tail proof behind a consumer-shaped boundary lemma. It should use C0.4.1 argument destructors and C0.4.2 return typing, and expose exactly the facts needed by the Resume replacement.

#### Approach
Assume the concrete branch facts produced by the RawCallTarget prefix split. Prove the side-effect, no-TypeError, state typing, and result typing conclusions in a form that the Resume can apply by `irule`/`drule` rather than unfolding the tail.

#### Not to try
Do not unfold the whole RawCallTarget evaluator tail in the final Resume once this boundary exists. Do not make the lemma statement depend on unrelated ExtCall generated premises.

### C0.4.4: Replace RawCallTarget Resume body with boundary-helper proof
- Kind: `proof_refactor`
- Risk: 2
- Work priority: 30
- Work units: 5
- Rationale: With C0.4.1-C0.4.3 available, the Resume proof is standard prefix splitting plus helper application. It is sequenced last within RawCallTarget.
- Dependencies: C0.4.3
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.4.4

#### Progress note
Only dependency metadata is changed; proof content is carried forward.

#### Summary
Replace the RawCallTarget Resume cheat after all RawCallTarget boundaries are proved. Use prefix splitting only to reach the boundary-helper assumptions, then apply C0.4.3 and project the required conjuncts.

#### Approach
Mirror nearby expression-call branch proofs. Split the evaluator prefix in a controlled way, close immediate errors, use C0.4.1/C0.4.2/C0.4.3 rather than unfolding the tail, and validate with `holbuild`.

#### Not to try
Do not begin before C0.4.3. Do not re-prove argument destructuring or flag typing inline in the Resume.

### C0.5: Task-scoped proof-integrity audit and unsigned commit
- Kind: `integration_validation`
- Risk: 1
- Work priority: 40
- Work units: 1
- Rationale: Final validation and commit hygiene are mechanical after all proof leaves complete. It is now directly blocked on C0.4.4 so it cannot appear early.
- Dependencies: C0.4.4
- Checkpoint: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0.5

#### Progress note
Dependency repaired to enforce final audit only after all proof leaves complete.

#### Summary
Run the task-scoped final build/audit only after C0.4.4. Confirm no scoped cheats/probes remain, no forbidden files were edited, and commit with `--no-gpg-sign`.

#### Approach
Run the prescribed `holbuild` target, inspect `git status`, stage only relevant tracked files under `semantics/prop`, and commit with `git commit --no-gpg-sign`. Update task state/plan notes to reflect completed proof progress.

#### Not to try
Do not stage known untracked artifacts such as legacy learnings/tmp helper files. Do not GPG-sign the commit.
