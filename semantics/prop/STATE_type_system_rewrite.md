# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit/build. Retry the required strategist replanning when oracle budget/tooling is available: call plan_oracle(mode="replace", component_id="C0", planning_reason="decompose/replace high-risk C0 after accepted blocked_report; no authorized frontier remains and completion is not valid", evidence_ids=["TO_type_system_rewrite-20260601T220715Z_m4250_t003","TO_type_system_rewrite-20260601T220715Z_m4246_t001","TO_type_system_rewrite-20260601T220715Z_m4247_t001","TO_type_system_rewrite-20260601T220715Z_m4241_t001"]).
- expected_goal_shape: No HOL goal should be active. query_plan currently shows high-risk [C0,C0.1], no scheduled leaf frontier, beginable now none, Oracle next none. Any proof/build action before a replacement/decomposition plan violates the structured gate.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300) only after a future PLAN authorizes a component/build; last focused build succeeded at tool_output:TO_type_system_rewrite-20260601T220715Z_m4239_t002.

## If This Fails
- If the required plan_oracle replace/decompose call again returns OracleBudgetExceeded, do not edit/build. Either retry once with minimal evidence IDs and no reads, or report end_session(outcome="blocked", blocked_kind="tooling_bug") citing repeated OracleBudgetExceeded and query_plan no-frontier evidence. If plan_oracle returns an authorized frontier, begin_component exactly as scheduled before edits/builds.

## Do Not Retry
- Begin C0.3-C0.7 or any ready-looking sibling while query_plan has high-risk [C0,C0.1] and no scheduled frontier.: Structured gate blocks all proof/edit/build work until the strategist replaces/decomposes C0 or provides an authorized frontier.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4250_t003
- Reapply the same straight-line `Cases_on run_ext_call` / `rename1 SOME result` probe in `Expr_Call_ExtCall_result_static_success`.: E0217 tested this and failed before helper matching with 9 input goals and a huge generated prefix; repeating it is tactic thrashing against a bad boundary.
  - evidence: episode:E0217
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4232_t001
- Solve the 5/9 generated-prefix goals individually, or use broad `simp`/`gvs`/`AllCaseEqs()` to mine an optional-driver IH.: Maintainer clarification and PLAN forbid generated-prefix reconstruction; evidence shows the goals are large and structurally wrong for straightforward proof.
  - evidence: episode:E0212
  - evidence: episode:E0217
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4165_t001
- Apply `extcall_static_projected_sound` or `extcall_static_projected_state_well_typed` at the top/current Resume boundary.: Earlier probe showed direct `irule` does not match and explicit specialization requires an unavailable unconditional driver IH.
  - evidence: episode:E0213
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4178_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4188_t001
- Call end_session(outcome='complete') because holbuild succeeds.: Build succeeds only for a cheated/restored baseline; proof-integrity completion is invalid while task obligations/cheats remain and PLAN has high-risk blocked components.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4239_t002
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4250_t003

## Reflection
### Tunnel Vision Check
- Outside-the-box route not yet explored: a future maintainer-authorized redesign could create a different branch container that prevents final postcondition conjunction fanout before run_ext_call; current PLAN does not authorize constructing it.
- We may be optimizing the wrong boundary, not the wrong tactic: the guarded continuation helpers look semantically right, but the current Resume source point cannot expose their consumer shape without generated-prefix plumbing.
- The current PLAN decomposition is not executable: after accepted blocked_report, C0/C0.1 are high-risk and no low-risk frontier exists despite ready-looking C0.3-C0.7 siblings.
- Do not retry branch-splitting tactics. The failure happened before helper matching, so a stronger helper or oracle-owned boundary redesign is needed, not a better `rename1`/`PairCases_on` sequence.
- A fresh expert should first question whether the mutual proof should suspend earlier/later around the final conjunction, or whether the task should stop exactly as requested because proof-boundary design became non-straightforward.

### What Went Wrong
- C0.2, C0.1.1, and C0.1.2 carry-forward checkpoints were reviewed and committed successfully, but the real C0.1.3.1 probe failed: straight-line run_ext_call splitting from the current static-success cheat produced 9 input goals and a >4KiB generated optional-driver prefix before reaching a concrete success branch (episode:E0217, tool_output:TO_type_system_rewrite-20260601T220715Z_m4232_t001).
- The prior assumption that guarded continuation helpers could simply be tested after a local split was false at this Resume boundary. The helper-fit point was never reached.
- The replacement blocked_report was accepted and committed, leaving the source restored/build-clean for the cheated baseline, but query_plan then had no authorized frontier and completion was invalid because remaining cheats/obligations still exist.
- The mandatory high-risk replanning call was attempted correctly with mode='replace', component_id='C0', but two consecutive calls failed OracleBudgetExceeded, creating an operational tooling blocker rather than a HOL proof blocker.

### Ignored Signals
- E0212 already showed the boundary was split into multiple goals before run_ext_call; the later straight-line split failed in the same family with 9 goals, confirming this was structural.
- Repeated evidence that generated optional-driver IH is guarded by a full monadic prefix means any path that requires it unconditionally or before concrete branch facts is suspect.
- Ready-looking siblings under a high-risk parent are not beginable; query_plan's scheduled frontier is authoritative.
- A clean holbuild of the cheated baseline is only restoration evidence, not task completion.

### Strategy Adjustments
- Next session should start with query_plan/git status, then immediately retry the plan_oracle replace/decompose call for C0 if the oracle budget is available; do not begin any ready-looking sibling until the PLAN provides an authorized frontier.
- If plan_oracle authorizes only a terminal stop/report, commit any task-memory update unsigned and report blocked/operator stop, not complete or unprovable.
- If a future plan authorizes proof redesign, insist on a Risk 1-2 leaf that first proves/probes the branch container prevents conjunction fanout; do not re-enter the old static-success Resume with the same run_ext_call split.
- Keep source restored and build-clean after any probe; untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` and `semantics/prop/tmp_helper.txt` should remain unstaged unless the user explicitly asks.

### Oracle Feedback
- Held: carry-forward checkpoint reviews for C0.2, C0.1.1, and C0.1.2 were accepted; the audited static prefix-error branches remain build-clean.
- Held: after E0217, oracle correctly replaced C0.1.3.1 with a blocked_report and warned not to continue C0.1.3.2.
- Missed reality earlier: the guarded-continuation probe plan still assumed a straight-line split would reach one concrete branch; holbuild showed 9 goals before the helper-fit point.
- Current oracle/tool issue: the required no-frontier replacement/decomposition call for C0 failed twice with OracleBudgetExceeded, so the session ended blocked on tooling.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4250_t003 - final query_plan: high-risk [C0,C0.1], no frontier/beginable component
- episode:E0217 - failed C0.1.3.1 proof-boundary probe; run_ext_call split fanned to 9 goals before helper fit
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4232_t001 - exact holbuild failure at `rename1`, 9 input goals, >4KiB generated prefix
- episode:E0218 - accepted blocked_report closure for C0.1.3.1
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4241_t001 - strategist accepted E0218; no PLAN changes, then no frontier remained
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4239_t002 - focused build clean after source restoration
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4246_t001 - first required plan_oracle replace/decompose failed OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4247_t001 - second required plan_oracle replace/decompose failed OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4248_t001 - final git status: only pre-existing untracked files remain
