# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C2.2
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First preserve the reviewed C2.1.1.13.4.4 checkpoint: inspect git status/diff, rerun holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600) if practical, then stage only relevant tracked files (currently source comment + DOSSIER + rendered STATE/LEARNINGS if changed) and commit; do not stage untracked scratch/test files. After that, query_plan shows C2.2 next but its allowed action recommends plan_oracle(mode="replace", component_id="C2.2", planning_reason="PLAN appears over-decomposed; request ancestor rebase/flatten instead of further tactical decomposition"), so ask the strategist before beginning C2.2 proof work unless a fresh query_plan explicitly allows begin_component('C2.2').
- expected_goal_shape: For the checkpoint verification, `vyperTypeStmtSoundnessTheory` should build successfully. For next proof work, C2.2 is the Expr_Attribute read/path resume; expect a cheated `Resume eval_all_type_sound_mutual[Expr_Attribute]` immediately after the completed Expr_Subscript resume, but current query_plan warns to seek a C2.2 rebase/flatten first.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If checkpoint holbuild fails, do not start C2.2; checkpoint_progress under the relevant active/last component with the exact failure and ask strategist if the failure is outside C2.1.1.13.4.4. If git status contains only the known reviewed checkpoint, commit it before proof work. If query_plan still says C2.2 is next but allowed actions only list plan_oracle replacement, call plan_oracle rather than begin/edit/build.

## Do Not Retry
- Begin/edit/build C2.2 immediately if query_plan still lists only plan_oracle replacement in allowed actions.: Latest query_plan lists C2.2 as next but explicitly says to call plan_oracle(mode='replace', component_id='C2.2') because the PLAN appears over-decomposed. Starting proof work would violate the structured gate.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40120_t003
- Stage or commit untracked `test_*`, `test_conj*`, or `SuspBugProbeScript.sml` files.: They are scratch/ad-hoc files unrelated to the stable proof checkpoint. Stage only tracked task-owned files and any rendered STATE/LEARNINGS changes.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40120_t002
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40095_t001
- Reopen or optimize the Expr_Subscript helper/integration proofs after E0708.: The local region has built and been reviewed. Any remaining cheats are later scheduled resumes, not local Expr_Subscript placeholders.
  - evidence: episode:E0708
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40115_t002
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40115_t001
- Reintroduce broad `simp[bind_def]` in `BaseTarget_Subscript` successful branch.: That exact broad simplification timed out earlier; the bounded `rewrite_tac[bind_def, return_def]` is verified and committed in the prior checkpoint.
  - evidence: episode:E0705
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40072_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40082_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach for next session: before proving Expr_Attribute, question whether C2.2's current plan is over-decomposed or stale now that Expr_Subscript is done; query_plan already suggested an oracle rebase/flatten rather than direct proof work.
- We are not optimizing the wrong theorem in the completed work: Expr_Subscript integration is built and audited, and remaining cheats are later resumes outside C2.1.1.13.4.4.
- The boundary-helper decomposition for Subscript was the right abstraction; it prevented duplication of index/get_Value/read-storage reasoning in the mutual Resume.
- Do not retry local Subscript tactics now; move on only after committing the reviewed checkpoint and resolving the C2.2 planning gate.
- A fresh expert should first question why query_plan says C2.2 is beginable but allowed actions recommend plan_oracle replace; treat that scheduling guidance as more important than starting another proof immediately.

### What Went Wrong
- STATE is stale because it still points to C2.1.1.13.4.3a. This session closed/reviewed E0707, committed the larger Subscript helper checkpoint as commit b6883b8f0, then began/closed/reviewed C2.1.1.13.4.4. The last reviewed C2.1.1.13.4.4 changes are not committed because the handoff interrupted after review.
- The old source comment at Expr_Subscript still mentioned temporary cheats even though the adapters were proved. It was corrected, rebuilt, and reviewed, but this small source change plus regenerated DOSSIER remain unstaged/uncommitted.
- There are many pre-existing untracked scratch/test files. They repeatedly show in git status and must not be staged or committed.

### Ignored Signals
- The C2.1.1.13.4.4 audit grep initially found only later unrelated cheats, plus a stale comment saying temporary cheats; that comment was a hygiene issue worth fixing before closure.
- Holbuild after the comment change emitted many checkpoint-invalid warnings but ultimately built successfully. Treat these as holbuild checkpoint replay noise unless a future build actually fails; do not delete checkpoints.
- query_plan after C2.1.1.13.4.4 review did not simply authorize begin_component C2.2 in allowed actions; it recommended a plan_oracle replace for over-decomposition. Preserve that in the cursor.

### Strategy Adjustments
- For post-integration/audit components, grep the exact local region for `cheat`/`FAIL_TAC` and distinguish component-local placeholders from later scheduled cheats before closing.
- After a reviewed proof checkpoint, commit immediately if build-clean and diffs are relevant; otherwise STATE becomes stale and future sessions must reconstruct what was already reviewed.
- For C2.2, avoid broad simplification over the strengthened mutual IH context; request strategist guidance/rebase first if the plan remains over-decomposed.

### Oracle Feedback
- Strategist accepted E0707 as the administrative duplicate BaseTarget_Subscript closure; no PLAN change was needed.
- Strategist accepted E0708: source readback showed Expr_Subscript delegates to the proved ordinary/place-as-ordinary/projection helpers, and the grep audit showed no local cheat or FAIL_TAC remains.
- The only current oracle/schedule wrinkle is query_plan's C2.2 allowed action recommending a replace/rebase despite listing C2.2 as beginable. Next session should resolve that gate before proof work.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40101_t001 - C2.1.1.13.4.3a verification build succeeded
- episode:E0707 - BaseTarget_Subscript administrative duplicate closure recorded/reviewed
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40115_t002 - `vyperTypeStmtSoundnessTheory` built successfully after Expr_Subscript integration audit/comment fix
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40115_t001 - grep audit: no `FAIL_TAC`; no Expr_Subscript/local-adapter cheats, only later scheduled resumes
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40113_t001 - readback of Expr_Subscript region showing adapter calls and place/projection conjunct
- episode:E0708 - C2.1.1.13.4.4 proved/reviewed
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40118_t001 - strategist accepted E0708 and requested stable checkpoint commit
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40120_t003 - latest query_plan: C2.2 next but allowed actions recommend plan_oracle replace/rebase
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40120_t002 - git status: reviewed C2.1.1.13.4.4 changes uncommitted plus untracked scratch files
