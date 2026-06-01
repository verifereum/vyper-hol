# PLAN

## Structured Components

### C0: Structural parent carry-forward for local ExtCall stop-state
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Previously high only because C0.1.1.2 remained a Risk-3 blocked proof subtree with no frontier. This update reclassifies that local subtree as an accepted terminal stop/report path under the TASK stop rule and adds a low-risk handoff leaf; no new ancestor-level proof strategy is introduced here.
- Required for completion: yes
- Progress transition: `refinement`
- Carries progress/evidence from: C0, E0063

#### Progress note
Minimal schema parent update to remove stale inherited high-risk rationale after local stop-state reclassification.

#### Summary
Schema parent included only to support the C0.1.1.2 augment. The local ExtCall branch is being handled as a terminal stop-state, not proof completion. Existing sibling components are not replanned by this update.

#### Approach
Delegate all concrete work to the C0.1.1.2 subtree. Do not infer permission to work on unrelated siblings from this parent wrapper.

#### Not to try
Do not use this wrapper to reopen the ExtCall proof or to edit outside `semantics/prop`.

### C0.1: Structural parent carry-forward for local ExtCall stop-state
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Previously high only because C0.1.1.2 remained a Risk-3 blocked proof subtree with no frontier. The child is now a low-risk terminal stop/report subtree; this parent carries that local classification without changing siblings.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.1, E0063

#### Progress note
Minimal parent update; prior sibling progress remains untouched.

#### Summary
Schema parent included only to support the C0.1.1.2 augment. The update does not add proof work outside the ExtCall stop-state branch.

#### Approach
Delegate concrete work to C0.1.1.2.5 and preserve existing sibling plans.

#### Not to try
Do not treat this as permission for broad proof search or unrelated cleanup.

### C0.1.1: Structural parent carry-forward for local ExtCall stop-state
- Kind: `proof`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: Previously high only because C0.1.1.2 was still classified as a blocked proof subtree. The child now has a low-risk terminal handoff leaf and no authorized theorem-proving frontier.
- Progress transition: `refinement`
- Carries progress/evidence from: C0.1.1, E0063

#### Progress note
Minimal parent update to clear stale inherited high-risk state; no broader redesign is performed.

#### Summary
Schema parent included only to support the C0.1.1.2 augment. The local ExtCall branch should report blocked/operator handoff rather than proof completion.

#### Approach
Delegate concrete work to C0.1.1.2.5. Preserve all accepted audit evidence from C0.1.1.2.0--C0.1.1.2.4.

#### Not to try
Do not resurrect removed child proof leaves or stale generated-prefix helpers.

### C0.1.1.1: Carry forward audit of the ExtCall helper interface
- Kind: `proof_interface_audit`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: This audit was already completed and remains relevant: the replacement strategy depends directly on the existing local helper theorem and place-elimination lemma found by the audit.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.1, E0034

#### Progress note
The prior audit is still valid under the direct-helper strategy.

#### Summary
No new executor work. Preserve the audited fact that `extcall_expr_sound_from_generated_ih` has the right boundary shape for ExtCall expression soundness and that `type_place_expr_Call_ExtCall_NONE` closes the place conjunct. Downstream work should rely on these names rather than rediscovering the ExtCall prefix.

#### Approach
No action required unless the build reports that one of the theorem names is not in scope. If that happens, stop and report the exact missing-name error rather than editing definitions.

#### Not to try
Do not repeat the audit by broad grepping or modifying the helper theorem; this component is carried forward as completed context.

### C0.1.1.2: ExtCall result branch terminal stop-state and operator-facing handoff
- Kind: `terminal_stop_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: The mathematical ExtCall proof remains unresolved, but the task contract explicitly says to stop on non-straightforward design/proof issues and the maintainer clarification forbids the failed generated-prefix recovery paths. E0063 establishes the source/build stop-state facts. The remaining work in this subtree is not renewed theorem proving; it is a mechanical terminal handoff/commit/report, so the subtree is executable at low risk.
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.0, C0.1.1.2.1, C0.1.1.2.2, C0.1.1.2.3, C0.1.1.2.4, E0051, E0055, E0056, E0058, E0063, TO_type_system_rewrite-20260601T081233Z_m1436_t001

#### Progress note
This replaces the prior high-risk blocked-proof parent classification with a terminal stop/report classification. The prior audits and failed-interface evidence still count; what changes is that no unresolved proof leaf remains authorized under this subtree.

#### Summary
- Treat the accepted E0063 state as the terminal local outcome for this subtree, not as proof completion of `Expr_Call_ExtCall_result`.
- The ExtCall Resume/cheat remains in `vyperTypeStmtSoundnessScript.sml`; this is intentional stop-state evidence under the TASK instruction to stop when the proof is not straightforward.
- Prior forbidden paths remain invalid: no broad ExtCall-prefix simplification, no manual generated-prefix witness plumbing, and no resurrection of `extcall_expr_sound_from_generated_driver_ih`.
- Existing children C0.1.1.2.0--C0.1.1.2.4 remain valid audits/cleanup; the only new executable action is a final mechanical handoff leaf.
- Completion of this subtree should report a blocked/operator-facing outcome, not claim the type-system rewrite proof is fully complete.

#### Description
This component no longer asks the executor to prove the ExtCall result branch. Prior episodes demonstrated that the apparent helper interface is not matchable in the live Resume, that the manual generated-prefix approach is brittle and forbidden, and that broad prefix cleanup violates the maintainer clarification. Since the TASK says to stop on unexpected proof/design issues and the accepted E0063 audit recorded a clean buildable stop-state with the ExtCall Resume still present, the correct local plan is to finish the handoff mechanics and report the blocked proof-interface issue.

#### Approach
Do not enter HOL proof search for the ExtCall branch. The executor should perform only the terminal handoff child: inspect status/diff, commit only relevant tracked `semantics/prop` progress-memory changes unsigned if present, and end/report that the proof remains blocked at the ExtCall result Resume. If the harness still exposes ready sibling proof components outside this subtree, do not reinterpret this component as authorizing them; this component's local outcome is a stop-state.

#### Not to try
- Do not retry `extcall_generated_driver_ih_elim_expr` by larger `qspecl_then` or ordered witness instantiation; E0055/E0056 showed this is the wrong consumer interface and it is forbidden by the maintainer clarification.
- Do not use broad `simp`/`gvs`/`AllCaseEqs()` over the whole ExtCall monadic prefix to recover the driver premise; E0051 showed it loses/splits the postcondition and the clarification explicitly forbids it.
- Do not recreate `extcall_expr_sound_from_generated_driver_ih`; it was removed as stale and absent in E0058/E0063 audits.
- Do not claim task completion or source proof completion merely because `holbuild` succeeds with the Resume/cheat still present.

#### Argument
The subtree's mathematical proof attempt has reached a proof-interface blocker, not a theorem proved state. The accepted invariant for this subtree is therefore operational: preserve the clean, audited source state and expose the unresolved ExtCall proof obligation honestly. E0063 supplies the facts needed for that invariant: the ExtCall Resume is still present, the invalidated helper is absent, no tracked source diff existed at audit time, and `vyperTypeStmtSoundnessTheory` built. Under the TASK's stop-on-non-straightforward rule, this is a valid terminal stop-state to report upward, provided no further proof edits are made and no forbidden proof paths are retried.

#### Definition design
No new definitions or semantic changes are authorized in this subtree. The failed design lesson is that the generated-driver eliminator is valid infrastructure but not a usable live Resume boundary. Any future proof-completion redesign, outside this terminal stop subtree, should capture a compact optional-driver IH before the ExtCall monadic prefix is generated and should first prove a matchable boundary probe; this plan does not authorize that future work.

#### Code structure
All files remain within `semantics/prop`. Do not edit evaluator/semantics definitions and do not edit outside `semantics/prop`. The terminal leaf may update only task-owned progress/state/dossier files if already regenerated by the harness and may commit those tracked changes unsigned. Do not stage untracked `semantics/prop/tmp_helper.txt` or `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md`; do not use `git add -A`.

### C0.1.1.2.0: Build-clean skeleton state is carried forward
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0052 established that failed wrapper insertion was removed and the theory returned to a build-clean cheat skeleton; no new work is needed.
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.0, E0052

#### Progress note
Prior proof/cleanup evidence remains valid under the stop-state replacement.

#### Summary
- Carry forward the restored source skeleton from E0052.
- The failed wrapper insertion remains absent.
- No source edits are authorized here.
- This component is closed evidence used by the final stop-state audit.

#### Approach
No action unless an audit discovers drift. If checked, verify only that the source remains in the restored skeleton state and that no failed wrapper code has been reintroduced.

#### Not to try
Do not use this component to re-open the ExtCall proof or to edit non-task files.

### C0.1.1.2.1: Opaque generated-driver predicate remains available infrastructure
- Kind: `infrastructure_lemma`
- Risk: 1
- Work priority: 1
- Work units: 0
- Rationale: E0053 proved the predicate and eliminator. They remain valid infrastructure, but they no longer authorize the stale helper-application proof path.
- Dependencies: C0.1.1.2.0
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.1, E0053

#### Progress note
The proved infrastructure remains in source/task context, but its former downstream proof use is invalidated by E0058.

#### Summary
- Carry forward the generated-driver predicate/eliminator from E0053.
- Treat it as retained infrastructure only.
- It is not a sufficient live proof interface for the ExtCall Resume.
- No new lemma work is scheduled here.

#### Approach
No action unless an audit discovers drift. Consumers must not unfold or extend this into generated-prefix adapter plumbing in this task.

#### Not to try
Do not infer from this infrastructure that `extcall_expr_sound_from_generated_driver_ih` exists or can be applied at the Resume site.

### C0.1.1.2.2: Abandoned wrapper-adapter path remains deleted
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 2
- Work units: 0
- Rationale: E0054 audited/removed the obsolete wrapper-adapter path; the stop-state replacement must not revive it.
- Dependencies: C0.1.1.2.0
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.2, E0054

#### Progress note
Prior cleanup remains valid and supports the explicit stop-state.

#### Summary
- Carry forward deletion of the abandoned wrapper-adapter path.
- This deletion is part of the proof-interface blocker record.
- No new source edits are required.
- Future work must not resurrect this path without a new plan.

#### Approach
No action unless an audit discovers drift. If checked, confirm no obsolete wrapper-adapter helper has reappeared in `semantics/prop`.

#### Not to try
Do not reintroduce wrapper adapters or generated-prefix witnesses as a workaround for the blocked ExtCall proof.

### C0.1.1.2.3: ExtCall result proof is blocked; preserve accepted stop report
- Kind: `stop_report_parent`
- Risk: 1
- Work priority: 3
- Work units: 0
- Rationale: The only child is the already accepted stop/report component. The stale proof child C0.1.1.2.3.2 is intentionally removed because E0058 shows it depended on an absent invalidated helper and would violate the accepted stop strategy.
- Dependencies: C0.1.1.2.0, C0.1.1.2.1, C0.1.1.2.2
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.3, E0057, E0058
- Invalidates prior progress/evidence: C0.1.1.2.3.2

#### Progress note
Replaces the mixed stop-plus-stale-proof parent with a pure stop-report parent. E0058 is accepted as valid evidence that the stale proof leaf must be removed.

#### Summary
- Carry forward E0057 as the accepted stop/report for the ExtCall result proof-interface blocker.
- Delete the stale helper-application proof leaf.
- The Resume remains `cheat QED`; this is intentional for the stop report.
- Downstream work may only audit/report this state, not attempt proof completion.

#### Description
This parent records the strategic conclusion of E0057 and E0058: the ExtCall result branch is not straightforward under the allowed proof architecture. The previously scheduled proof leaf was a stale remnant and is no longer executable.

#### Not to try
Do not prove the old helper, do not specialize the generated IH from the top-level Resume prefix, and do not use broad cleanup over the whole monadic ExtCall prefix.

#### Argument
The proof attempt is blocked because the live Resume context does not provide a matchable premise for the generated optional-driver IH without forbidden generated-prefix reconstruction. Since the task explicitly says to stop on non-straightforward proof/design issues, the correct branch outcome is an accepted stop report, not another proof decomposition.

#### Definition design
No definitions are changed. The failed interface is the attempted bridge from the generated optional-driver IH to the ExtCall success continuation; it must not be hidden behind a resurrected helper unless a future task redesigns and probes that interface from scratch.

#### Code structure
Keep source proof code as restored. Maintain stop/blocker documentation in task-owned files under `semantics/prop`; do not add proof helpers or wrapper adapters.

### C0.1.1.2.3.1: Stop/report ExtCall result proof-interface blocker
- Kind: `stop_report`
- Risk: 1
- Work priority: 0
- Work units: 0
- Rationale: E0057 validly closed this component: the source remains with the original `Expr_Call_ExtCall_result` cheat, the build-clean restored state was checked, and the blocker was recorded under `semantics/prop`.
- Dependencies: C0.1.1.2.0, C0.1.1.2.1, C0.1.1.2.2
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.1.2.3.1, E0057

#### Progress note
Accepted stop/report evidence remains the authoritative closure for this branch.

#### Summary
- Carry forward the accepted E0057 stop/report.
- Preserve the original `Expr_Call_ExtCall_result` cheat.
- Record the blocker from E0055/E0056/E0058 rather than attempting proof plumbing.
- This component is already closed; no redo is requested.

#### Approach
No proof work remains. If the workflow asks for evidence, cite E0057/E0058 and the fact that no source proof edits were made after the stop decision.

#### Not to try
Do not reopen this as a proof component or attempt to discharge the Resume cheat here.

### C0.1.1.2.4: Final stop-state audit, unsigned commit, and operator report
- Kind: `proof_audit`
- Risk: 1
- Work priority: 4
- Work units: 1
- Rationale: After E0058, only a mechanical final audit/report remains: verify the stop-state has no source proof drift, commit only relevant task-owned progress files unsigned if appropriate, and report that the ExtCall proof remains blocked. No theorem proof is attempted.
- Dependencies: C0.1.1.2.3.1
- Checkpoint: yes
- Progress transition: `replacement`
- Carries progress/evidence from: C0.1.1.2.4, E0057, E0058
- Invalidates prior progress/evidence: C0.1.1.2.3.2

#### Progress note
Replaces the old final proof/build audit, which depended on a successful helper/Resume proof, with a final stop-state audit/report that depends only on the accepted stop component.

#### Summary
- Inspect git status/diff before committing.
- Confirm `vyperTypeStmtSoundnessScript.sml` still contains the original `Expr_Call_ExtCall_result` cheat and no resurrected helper/proof edits.
- Stage only relevant tracked task-owned progress/documentation files under `semantics/prop`; do not stage untracked tmp/legacy files unless explicitly intended by the maintainer.
- Commit unsigned if the checked diff is only the stop-state documentation/progress update.
- Report to the operator that the ExtCall result proof remains blocked by the accepted proof-interface issue.

#### Approach
Run a narrow audit: status/diff, grep for `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`, and optionally grep that `extcall_expr_sound_from_generated_driver_ih` is absent. If the diff contains only task-owned progress docs, make a small unsigned checkpoint commit; otherwise stop and report the unexpected diff. Do not run or edit proof code except for read-only audit commands.

#### Not to try
Do not attempt to finish `Expr_Call_ExtCall_result`, do not create the absent helper, and do not stage untracked scratch files such as `tmp_helper.txt` or legacy files unless the maintainer explicitly asks for them.

### C0.1.1.2.5: Commit terminal progress memory and end with blocked ExtCall handoff
- Kind: `terminal_handoff`
- Risk: 1
- Work priority: 100
- Work units: 1
- Rationale: This is mechanical bookkeeping/reporting only. The proof/build facts were already established by E0063 and accepted in review; the executor must not perform proof edits or broad builds while the local outcome is a stop-state.
- Dependencies: C0.1.1.2.4
- Checkpoint: yes
- Carries progress/evidence from: C0.1.1.2.4, E0063, TO_type_system_rewrite-20260601T081233Z_m1436_t001

#### Progress note
Added because after E0063 review the plan still had no low-risk frontier and no legal terminal action inside this subtree. This leaf is strictly bookkeeping/reporting; it does not reopen the ExtCall proof.

#### Summary
- Inspect `git status` and tracked diff under `semantics/prop`.
- If only task-owned tracked progress/state/dossier files are changed, commit them with `git commit --no-gpg-sign`; otherwise stop and report the unexpected diff.
- Never stage untracked tmp/legacy files and never use `git add -A`.
- End/report the task as blocked at the ExtCall result proof-interface issue, with the Resume/cheat intentionally still present.
- Do not run new ExtCall proof tactics or edit source proof scripts.

#### Description
This leaf gives the executor a legal final action after E0063 review. It turns the accepted stop-state audit into an operator-facing handoff: preserve any regenerated tracked progress-memory files with an unsigned checkpoint commit if safe, then report that the task cannot honestly be marked proof-complete because `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` still contains the ExtCall Resume/cheat.

#### Statement
Operational leaf, no HOL theorem statement. Expected checked facts to cite from prior evidence: ExtCall Resume present in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, `extcall_expr_sound_from_generated_driver_ih` absent, and `vyperTypeStmtSoundnessTheory` built in E0063.

#### Approach
Run only status/diff inspection commands needed for safe commit hygiene. Stage tracked task-owned progress files with `git add -u semantics/prop/<file>` or an equivalently narrow command; commit with `--no-gpg-sign` if the diff is exactly the expected memory/progress update. Then close the component/report a blocked stop outcome, explicitly saying that no source proof completion was attempted after E0063.

#### Not to try
- Do not run `holbuild` as a new proof attempt if the harness still blocks builds on high-risk ancestors; the relevant build evidence is already E0063.
- Do not edit `vyperTypeStmtSoundnessScript.sml` in this leaf.
- Do not stage untracked files or unrelated repository files.
- Do not report `complete`; report blocked/operator handoff unless an ancestor-level strategist later reclassifies the entire task outcome.

### C0.1.2: Prove the focused static ExtCall success continuation
- Kind: `theorem_proof`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: After C0.1.1, the static branch should no longer require generated-prefix reconstruction: expression-list soundness, target decoding, calldata/run/update success facts, and `value_opt = NONE`/`arg_vals = TL vs` are local assumptions. Existing continuation helpers handle the remaining preservation/result typing.
- Dependencies: C0.1.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.2

#### Summary
Discharge the static success placeholder produced by C0.1.1. Use local success assumptions plus `run_ext_call_accounts_well_typed` and `extcall_success_continuation_sound_cond_driver_ih`. Specialize the generated optional-driver IH only under `returnData = [] /\ IS_SOME drv`.

#### Approach
Work only inside the focused static Resume/placeholder. First derive `accounts_well_typed accounts'` from the successful `run_ext_call`; then invoke the conditional-driver continuation helper. Error-prefix reasoning should no longer appear in this component.

#### Not to try
Do not unfold the entire ExtCall evaluator or reconstruct static prefix facts; C0.1.1 must have made them local.

### C0.1.3: Prove the focused nonstatic ExtCall success continuation
- Kind: `theorem_proof`
- Risk: 2
- Work priority: 2
- Work units: 5
- Rationale: After C0.1.1, the nonstatic branch has explicit successful target and transfer amount decoding. Existing helper `extcall_nonstatic_args_runtime_typed_dest` and continuation lemmas make the remainder mirror static.
- Dependencies: C0.1.1
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.1.3

#### Summary
Discharge the nonstatic success placeholder produced by C0.1.1. Use local assumptions for `SOME amount`, argument tail, successful call/update facts, and conditional driver IH. The proof mirrors the static success continuation with value transfer present.

#### Approach
Work only inside the focused nonstatic placeholder. Derive account well-typedness from `run_ext_call_accounts_well_typed`, then apply the conditional-driver continuation helper. Keep optional-driver specialization branch-local and conditional.

#### Not to try
Do not redo nonstatic prefix splitting here; C0.1.1 owns all target/value decoding and monadic prefix cases.

### C0.2: Prove RawCallTarget mutual expression case
- Kind: `theorem_proof`
- Risk: 2
- Work priority: 1
- Work units: 5
- Rationale: Downstream call-target branch remains a known cheat, but should be standard after ExtCall because the mutual theorem infrastructure and raw-call builtin typing lemmas are already present. It depends on the ExtCall checkpoint so the executor does not split attention before the current blocker is resolved.
- Dependencies: C0.1.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.2@previous

#### Summary
- After ExtCall is proved, remove the `eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` cheat.
- Follow the existing call-expression proof style and raw-call helper lemmas.
- Keep edits in `semantics/prop/vyperTypeStmtSoundnessScript.sml`.
- Do not start this before the ExtCall checkpoint closes.

#### Statement
`Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]` must be proved without `cheat`.

#### Approach
Use the same mutual-theorem assumptions and evaluator unfolding pattern as adjacent call cases, but only after ExtCall is closed. Mine existing raw-call local helper lemmas before introducing new ones.

#### Not to try
Do not work on RawCallTarget while ExtCall remains blocked; doing so violates the task priority and risks hiding the central proof-boundary issue.

### C0.3: Discharge raw_call_return_type_well_formed arithmetic/type lemma
- Kind: `infrastructure_lemma`
- Risk: 2
- Work priority: 2
- Work units: 3
- Rationale: The remaining cheat is localized to `vyperTypeBuiltinsScript.sml` and appears to be arithmetic/type-formation cleanup around `word_size`, `type_slot_size`, and the `flags.rcf_max_outsize < dimword(:256)` bound. No semantic redesign is involved.
- Dependencies: C0.2
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.3@previous

#### Summary
- Remove the localized `raw_call_return_type_well_formed` cheat in `semantics/prop/vyperTypeBuiltinsScript.sml`.
- Prove the arithmetic/type well-formedness obligations directly.
- Keep any helper lemmas local unless they are already useful elsewhere.
- Run focused builds after the proof.

#### Statement
`raw_call_return_type_well_formed` as currently stated in `semantics/prop/vyperTypeBuiltinsScript.sml`, without changing evaluator or semantics definitions.

#### Approach
Inspect the current theorem statement and unfold only the relevant raw-call return type and well-formedness definitions. Use existing arithmetic libraries/lemmas for word-size and dimword inequalities; do not broaden the builtin typing interface.

#### Not to try
Do not modify raw-call semantics or builtin typing definitions to make this lemma easier unless a separate unprovability report is produced.

### C0.4: Update task status files and make unsigned progress commit after cheats are removed
- Kind: `status_update_commit`
- Risk: 1
- Work priority: 3
- Work units: 2
- Rationale: Mechanical repository hygiene required by the task once proofs are complete. It does not affect theorem truth, but must obey the no-outside-semantics/prop and no-GPG constraints.
- Dependencies: C0.3
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.4@previous

#### Summary
- Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and/or `STATE_type_system_rewrite.md` to reflect completed proofs.
- Audit that source edits stayed under `semantics/prop`.
- Commit with `git commit --no-gpg-sign` only.
- Do not commit before proof obligations are actually discharged.

#### Statement
Repository/status action, not a HOL theorem.

#### Approach
Use `git status` to confirm paths, update task memory accurately, and commit only relevant `semantics/prop` changes. The commit message should mention ExtCall/RawCallTarget/builtin cheat removal if all are completed.

#### Not to try
Do not use default `git commit` if it may GPG-sign. Do not include unrelated files outside `semantics/prop`.

### C0.5: Final zero-cheat validation for vyperSemanticsHolTheory
- Kind: `validation`
- Risk: 1
- Work priority: 4
- Work units: 2
- Rationale: Mechanical final check specified by the task and plan. It depends on all known reachable cheats being removed first.
- Dependencies: C0.4
- Checkpoint: yes
- Progress transition: `carry_forward`
- Carries progress/evidence from: C0.5@previous

#### Summary
- Run `holbuild build vyperSemanticsHolTheory`.
- Confirm zero CHEAT warnings reachable from `vyperSemanticsHolTheory`.
- If focused builds pass but final reachable-cheat audit finds a new in-scope cheat, stop and report/re-plan.
- This is the task completion checkpoint.

#### Statement
Validation target: `holbuild build vyperSemanticsHolTheory` succeeds with zero reachable fresh-stack CHEAT warnings.

#### Approach
Run the final build after all source cheats in scope are removed and committed/statused as appropriate. Record exact output in the task state.

#### Not to try
Do not treat `vyperTypeStmtSoundnessTheory` alone as final validation; the task completion scope is `vyperSemanticsHolTheory` reachable-cheat cleanliness.
