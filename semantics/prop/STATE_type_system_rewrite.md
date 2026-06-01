# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.2.1.3.3
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Open the static Resume around `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`; remove/replace the current `FAIL_TAC` probe left in the `Cases_on x'0` area, then continue only C0.2.1.3.3. First determine which `x'0` branch is success (`check success` succeeds) and put `extcall_success_continuation_state_well_typed`/`extcall_after_state_update_tail_sound` on that branch, not at the top of the Resume.
- expected_goal_shape: After linear ExtCall prefix split in the static Resume: assumptions include generated `driver_ih` as a full prefix-guarded implication, `run_ext_call ... NONE ... = SOME (...)`, `accounts_well_typed` for returned accounts, `runtime_consistent env cx args_st`, and a projected conclusion `state_well_typed st'`. The hard subgoal is the conditional driver-IH premise for the success continuation, under `returnData = [] /\ IS_SOME drv`, using generated prefix facts already split locally.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)

## If This Fails
- If the final driver-IH discharge cannot be solved by matching the saved generated IH after the success branch is concrete, checkpoint_progress with the exact holbuild goal and close C0.2.1.3.3 as stuck/risk_mismatch only if terminal. Do not broaden to top-level projected helpers, whole-prefix AllCaseEqs/gvs, or generated-prefix adapter theorems.

## Do Not Retry
- Apply `extcall_static_projected_state_well_typed` or `extcall_nonstatic_projected_state_well_typed` directly at a suspended Resume entry goal.: The available generated optional-driver IH is a full prefix-guarded implication with an extra place-expression conjunct, while these helpers require a compact unconditional driver-IH premise; direct `irule`/`drule_all` failed or timed out.
  - evidence: episode:E0133
  - evidence: episode:E0139
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2812_t001
- Use broad `gvs`/`simp`/`AllCaseEqs()` over the whole generated ExtCall prefix to recover the driver premise.: Maintainer/PLAN forbids this, and earlier attempts timed out with large generated-prefix goals. It is a decomposition smell, not a tactic problem.
  - evidence: episode:E0135
  - evidence: episode:E0136
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2869_t001
- Leave or commit the current `FAIL_TAC` probe in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]`.: The active source is partial and intentionally failing for inspection; it must be removed/replaced before a clean build or any commit.
  - evidence: episode:E0140
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2959_t001
- Stage untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They were pre-existing/untracked working-tree artifacts and not part of stable proof progress. Use `git add -u semantics/prop` or explicit tracked paths only.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2906_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2923_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet exhausted: instead of using `extcall_success_continuation_state_well_typed`, try applying `extcall_after_state_update_tail_sound` directly once `evaluate_type`/`get_tenv` facts are established, because it may match the concrete post-update tail better and avoid the `do assert T; update...` wrapper.
- A fresh expert would first question the branch orientation after `Cases_on x'0`: prior attempts may have placed success-continuation logic on the wrong branch. Verify which subgoal corresponds to `success = T` before adding tail proof.
- The PLAN decomposition is still plausible: linear branch-local proof, not top-level compact helper. The danger is accidentally optimizing the wrong consumer theorem (`extcall_static_projected_state_well_typed`) rather than the concrete Resume branch.
- Do not retry tactics blindly; if the saved generated IH cannot be consumed after the branch is concrete, the missing piece is a small local projection of the expression half of the generated IH, not a larger simplifier search.
- Current source is partial and contains a probe; do not commit until the probe is removed and holbuild succeeds.

### What Went Wrong
- C0.2.1.4.2 was successfully proved and committed, but its direct consumer C0.2.1.4.3 failed; oracle replaced the nonstatic plan with a linear Resume proof and rescheduled C0.2.1.3.3 first.
- For C0.2.1.3.3, I began probing the static Resume. The proof reached the run-ext-call success area, but the generated driver IH remained a full prefix-guarded implication. Current partial source has `FAIL_TAC` in the static Resume branch.
- An attempted `irule extcall_success_continuation_state_well_typed` placement after `Cases_on x'0` still produced a remaining projected `state_well_typed st'`/`MATCH_MP_TAC No match` or branch-not-solved failure, suggesting the branch orientation or match point was wrong.

### Ignored Signals
- The `Cases_on x'0 >> gvs[return_def, raise_def] >- (...)` shape is easy to misread: since `x'0` is the success flag, the `F` branch is the reverted/error branch and the `T` branch is the continuation branch. Verify from holbuild, do not assume.
- The generated IH assumption printed by holbuild is an implication from the entire ExtCall prefix; any attempt to consume it before those prefix equations are local concrete assumptions will reproduce E0133/E0139.
- Current working tree has untracked legacy/tmp files predating this handoff; do not stage them. Only stage relevant tracked semantics/prop changes after a clean build.

### Strategy Adjustments
- Next session should start by reading the current static Resume lines and removing the `FAIL_TAC` probe; do not run holbuild expecting success until that is done.
- Use the proved helper `extcall_static_projected_state_well_typed` only as a script template, not as a direct theorem at the Resume goal.
- At the final success branch, explicitly establish small facts (`accounts_well_typed`, `runtime_consistent`, `well_formed_type`/`evaluate_type`, `get_tenv`) before applying the tail theorem.
- For driver IH discharge, prefer `strip_tac` on `returnData = [] /\ IS_SOME drv`, then use the saved `driver_ih` by matching its generated implication after prefix equations are in assumptions; avoid broad simplification over the whole prefix.

### Oracle Feedback
- Held: Oracle diagnosis that top-level projected-helper consumption is wrong was confirmed again by E0139; the generated IH is not compact at Resume entry.
- Held: Proving compact boundary lemmas outside the Resume works; C0.2.1.4.2 built cleanly and was committed.
- Missed/needs care: The later oracle repair for nonstatic changed scheduling to static C0.2.1.3.3; despite Risk 2, the exact branch orientation and generated IH discharge remain delicate.
- Current oracle direction is binding: work active C0.2.1.3.3 first, branch-local linear static proof; no unrelated work and no direct `extcall_static_projected_state_well_typed` retry.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2920_t001 - C0.2.1.4.2 nonstatic projected-state boundary lemma build clean
- episode:E0138 - C0.2.1.4.2 proved/reviewed and committed
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2935_t001 - C0.2.1.4.3 direct `irule` of boundary lemma failed in Resume
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2937_t001 - C0.2.1.4.3 direct `drule_all` of boundary lemma failed in Resume
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2939_t001 - after reverting C0.2.1.4.3 experiment, target build clean
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2942_t001 - oracle replacement plan: static C0.2.1.3.3 is Oracle next, branch-local linear proof
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2949_t001 - static success probe reached generated prefix-guarded driver IH context
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2955_t001 - attempted success-continuation placement had branch/subgoal mismatch
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2959_t001 - revised static branch probe still not closed; current source partial
- episode:E0140 - non-terminal checkpoint for current partial C0.2.1.3.3 probe evidence
