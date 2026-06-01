# PLAN

## Structured Components

### C0: Record ExtCall proof-boundary blockage and stop further proof work
- Kind: `blocked_report_subtree`
- Risk: 2
- Work priority: 0
- Work units: 0
- Rationale: This is no longer a proof-completion subtree. The proof-boundary issue has checked evidence (E0066/E0067/E0068/E0070/E0072), and the remaining work is bounded task-local reporting/audit/commit work inside `semantics/prop`. Risk is standard because the proof theorem remains intentionally cheated, but this component's deliverable is the required stop/report state under the task instructions, not another proof attempt.
- Required for completion: yes
- Supersedes: C0, C0.1, C0.2, C0.3, C0.4, C0.5
- Progress transition: `replacement`
- Carries progress/evidence from: E0066, E0067, E0068, E0070, E0071, E0072, TO_type_system_rewrite-20260601T081233Z_m1655_t001, TO_type_system_rewrite-20260601T081233Z_m1656_t001, TO_type_system_rewrite-20260601T081233Z_m1657_t002, TO_type_system_rewrite-20260601T081233Z_m1659_t001
- Invalidates prior progress/evidence: C0.2, C0.3, C0.4, C0.5

#### Progress note
Replaces the failed proof-completion C0 subtree with a terminal stop/report subtree. E0072 validates that the sanitized C0.1 boundary failed for the same structural reason as earlier attempts: routine simplification of an argument-error branch sees the full generated optional-driver prefix. Therefore the previous static/nonstatic/cleanup leaves are invalidated; they depended on C0.1 isolating the argument-success branch, which did not happen.

#### Summary
- Scope remains only the ExtCall result cheat in `semantics/prop/vyperTypeStmtSoundnessScript.sml` and task-local progress files under `semantics/prop`.
- The theorem has not been shown false, but all authorized straightforward proof-boundary attempts have failed with checked generated-prefix evidence.
- Do not attempt C0.2/C0.3-style static/nonstatic branch proofs: their prerequisite boundary was refuted by E0072.
- The source must remain restored to `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]: cheat QED` unless a future replacement proof architecture is supplied.
- Complete this subtree by updating task-local plan/state notes, auditing the restored baseline build, and committing/reporting unsigned.
- No evaluator/semantics definitions and no files outside `semantics/prop` may be edited.

#### Description
The previous C0 plan tried to turn the maintainer clarification into a low-risk proof path: validate a sanitized Resume shell, then prove static and nonstatic success branches. E0072 refutes that plan. Even after explicit expression-list IH discharge, the `args_res = INR y` branch still carries the full generated optional-driver success-prefix implication, and `simp[no_type_error_result_def]` times out on a >4KiB goal. Because this is exactly the proof-interface symptom the task says to stop on, the responsible next action is not another tactic variant but a clear blocked report and source audit.

#### Approach
Do not edit the proof body except to ensure it is restored to the intentional `cheat` baseline. Update `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and, if used by the workflow, `semantics/prop/STATE_type_system_rewrite.md` to record E0072 as the latest failed proof-boundary probe and to state that old C0.2-C0.5 are unauthorized/invalidated. Then run the target build only to verify the restored cheated baseline, not to claim proof completion.

#### Not to try
Do not retry `simp`, `gvs`, `AllCaseEqs()`, or branch-local variants on the generated-prefix goal. Do not resurrect old static/nonstatic leaves as executable work. Do not introduce a long generated-prefix adapter theorem or try to recover the optional-driver IH from the top-level Resume context. Do not change evaluator definitions or edit outside `semantics/prop`.

#### Argument
The mathematical proof of ExtCall soundness is not being completed in this subtree. The strategic conclusion is negative but checked: the current induction/Resume boundary exposes an optional-driver IH as a large implication guarded by the entire ExtCall monadic success prefix. That implication pollutes even argument-error branches where the driver cannot be relevant. Since ordinary branch simplification must inspect the enclosing case expression and prefix, the live proof obligation is not a small source-level ExtCall branch proof. A future successful proof likely requires a different induction/suspend boundary or a small validated source-level continuation theorem whose statement does not carry this generated prefix into irrelevant branches. This subtree records that boundary failure and preserves proof integrity by stopping.

#### Definition design
No definition changes are authorized. The failed proof interface is the current generated optional-driver IH exposed by `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`; it is not suitable as a consumer boundary because it requires carrying/reconstructing a full generated ExtCall prefix before the proof reaches concrete success-continuation branches. A future replacement plan must first provide a probe showing that its boundary can close the `eval_exprs` argument-error branch without the generated driver prefix in the live simplification goal. Until such a probe exists, no downstream ExtCall branch proof is executable.

#### Code structure
All work stays in `semantics/prop`. Keep `semantics/prop/vyperTypeStmtSoundnessScript.sml` at the restored intentional-cheat baseline for `Expr_Call_ExtCall_result`. Put report updates in `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` and state/cursor updates in `semantics/prop/STATE_type_system_rewrite.md` if that file is tracked for this task. Do not move or edit evaluator/semantics code outside this directory. If committing, use `git commit --no-gpg-sign` and include only task-owned tracked files.

### C0.1: Update task-local ExtCall blockage report after E0072
- Kind: `source_cleanup`
- Risk: 1
- Work priority: 0
- Work units: 2
- Rationale: This is mechanical documentation/state cleanup based on already accepted checked evidence. It does not require new proof search or theorem statements.
- Supersedes: C0.1
- Progress transition: `replacement`
- Carries progress/evidence from: E0072, TO_type_system_rewrite-20260601T081233Z_m1655_t001, TO_type_system_rewrite-20260601T081233Z_m1659_t001
- Invalidates prior progress/evidence: C0.2, C0.3, C0.4, C0.5

#### Progress note
Turns the accepted E0072 proof-boundary failure into the current task-local plan/state record and explicitly removes the old downstream proof leaves from the executable story.

#### Summary
- Edit only task-local report/state files under `semantics/prop`.
- Record that E0072 supersedes the previous sanitized-boundary proof plan.
- State that C0.2-C0.5 depended on the failed C0.1 boundary and are no longer authorized.
- Preserve the message that the theorem is not proved false; the blockage is proof-boundary/goal-shape.
- Preserve the maintainer constraints: no evaluator changes, no broad generated-prefix cleanup, no long adapter theorem.

#### Statement
Documentation deliverable: `TYPE_SYSTEM_REWRITE_PLAN.md`/state notes say the latest C0 proof-completion subtree is stopped after E0072; `eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` remains an intentional cheat pending a new proof architecture.

#### Approach
Add a short dated update near the existing ExtCall blockage section. Cite E0072 and m1655/m1656/m1657/m1659: the sanitized shell discharged the `eval_exprs` IH explicitly but timed out on the `args_res = INR y` branch because the generated optional-driver prefix was still present. Replace any language implying C0.2-C0.5 are ready with language saying they are invalidated unless a new boundary first isolates the argument-success branch.

#### Not to try
Do not edit `vyperTypeStmtSoundnessScript.sml` to try a new proof while doing this component. Do not soften the report into 'maybe try another simplifier'; the accepted evidence is a stop condition. Do not add speculative proof sketches as executable plan leaves.

### C0.2: Audit restored cheated baseline and absence of unauthorized ExtCall proof edits
- Kind: `integration_validation`
- Risk: 1
- Work priority: 10
- Work units: 1
- Rationale: The source was already restored and build-clean in m1656/m1657; this is a mechanical verification after documentation edits.
- Dependencies: C0.1
- Checkpoint: yes
- Supersedes: C0.5
- Progress transition: `replacement`
- Carries progress/evidence from: TO_type_system_rewrite-20260601T081233Z_m1656_t001, TO_type_system_rewrite-20260601T081233Z_m1657_t002

#### Progress note
Carries forward the restored baseline evidence and replaces the old 'remove cheat after proof' integration component with a proof-integrity audit that the cheat remains intentional and no partial failed proof text remains.

#### Summary
- Verify `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` is exactly back to `cheat QED` or otherwise intentionally cheated.
- Run `holbuild` for `vyperTypeStmtSoundnessTheory` only to check the restored baseline still builds.
- Confirm no tracked proof edits from failed probes remain.
- This build is not proof completion; it only validates the honest stopped state.

#### Statement
Audit deliverable: `vyperTypeStmtSoundnessTheory` builds with the intentional ExtCall result cheat, and the working tree has no unintended tracked proof changes outside the task-local report/state updates.

#### Approach
Use grep/read around the ExtCall Resume and run the existing target build with a normal timeout. Inspect tracked diff/status before committing. If the build fails or the proof body is not restored to the intentional cheat, stop and report a tooling/source-integrity issue rather than repairing proof tactics.

#### Not to try
Do not interpret a successful build as soundness completion. Do not remove the cheat. Do not stage untracked scratch/legacy files unless the operator explicitly asks.

### C0.3: Commit/report the stopped ExtCall state unsigned
- Kind: `task_handoff`
- Risk: 1
- Work priority: 20
- Work units: 1
- Rationale: Mechanical task handoff. The task explicitly requires commits as progress is made and forbids GPG signing; the only proof-sensitive requirement is not to include unauthorized files.
- Dependencies: C0.2
- Checkpoint: yes
- Carries progress/evidence from: E0072

#### Progress note
Finalizes the replacement C0 stop/report subtree after the E0072 failure and audit.

#### Summary
- Stage only tracked task-owned files under `semantics/prop` that were intentionally updated.
- Commit with `git commit --no-gpg-sign`.
- Final report must say the ExtCall proof remains blocked, not completed.
- Mention that old proof leaves are invalidated and future work needs a new proof boundary/induction-suspend interface.

#### Statement
Handoff deliverable: an unsigned commit records the task-local stop/report update, or if there are no tracked changes to commit, the final report explicitly states that no commit was needed because the accepted evidence was already recorded.

#### Approach
Check `git status --short` and `git diff -- semantics/prop`. Stage only the intended report/state files. Use an unsigned commit message such as `Report ExtCall boundary failure after E0072`. If untracked scratch files are present, leave them untracked unless they are explicitly part of the task-owned report.

#### Not to try
Do not use a signed commit. Do not commit files outside `semantics/prop`. Do not commit failed proof experiments or generated logs.
