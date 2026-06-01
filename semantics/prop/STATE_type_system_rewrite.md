# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/PLAN_type_system_rewrite.md
- next_action: Do not edit/build/prove under the current task contract. The task is blocked at the required static ExtCall cheat. Resume only after explicit maintainer/user approval of a new static ExtCall proof architecture or changed scope; then call plan_oracle to replace/decompose the blocked C0/C0.2 static ExtCall gate before any proof-script edits.
- expected_goal_shape: No HOL goal expected. query_plan shows C0/C0.2/C0.2.1/C0.2.1.3/C0.2.1.3.3 high-risk blocked with no scheduled leaf frontier, no beginable component, and no Oracle next. `eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` remains an intentional explicit cheat, so zero-cheat completion is not satisfied.
- verify_with: If a new architecture is approved later: first run git status and query_plan; after plan_oracle creates an authorized low-risk frontier, begin the scheduled component and verify with holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300). Under the current PLAN, holbuild is blocked by the risk gate.

## If This Fails
- If query_plan still shows no frontier, do not handoff-loop or proof-search; report blocked to the operator. If plan_oracle creates a new frontier after explicit approval, begin exactly the scheduled component before edits/builds. Leave untracked semantics/prop/LEARNINGS_type_system_rewrite.legacy.md and semantics/prop/tmp_helper.txt unstaged.

## Do Not Retry
- Prove static ExtCall by deriving the compact driver premise from generated driver_ih using mp_tac driver_ih >> simp[], broad gvs, AllCaseEqs(), drule_all, metis_tac, or a long generated-prefix adapter theorem.: E0144/E0149 show this route times out and violates both PLAN not-to-try guards and the maintainer clarification that only straightforward branch-local proof is allowed.
  - evidence: episode:E0144
  - evidence: episode:E0149
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3090_t001
- Proceed to nonstatic ExtCall, RawCallTarget, wrapper, or final zero-cheat audit components while static ExtCall remains intentionally cheated.: Final C0 blocked_task_gate says downstream leaves are invalidated/not executable because the required static ExtCall gate blocks completion.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3147_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3159_t003
- Describe the task as complete or zero-cheat clean because a previous holbuild succeeded.: The build succeeded only on an intentional-cheat baseline; proof-integrity completion is not satisfied while Expr_Call_ExtCall_result_static remains cheated, and current holbuild is PLAN-gated blocked.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3137_t004
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3138_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3152_t002
- Stage or commit untracked semantics/prop/LEARNINGS_type_system_rewrite.legacy.md or semantics/prop/tmp_helper.txt.: They are known pre-existing untracked artifacts outside stable task progress; commits should stage only relevant tracked task-local files with explicit paths/add -u and --no-gpg-sign.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3159_t002
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3150_t002

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet authorized: avoid the generated Resume IH entirely by changing mutual theorem/suspension granularity or proving a new evaluator-specific continuation theorem before the generated ExtCall prefix is introduced.
- We were optimizing the static ExtCall Resume consumer proof, but accepted evidence says the current theorem/proof interface is the wrong abstraction under the straightforward-proof constraint; further tactic tuning is counterproductive.
- The prior deep PLAN decomposition was not the right abstraction after E0149/E0150: carry-forward leaves were cleanup/status bookkeeping, then the strategist consolidated the task into a blocked_task_gate.
- A fresh expert should first question the proof boundary for the generated optional-driver IH, not individual simp/gvs tactics, and should check the source line with the intentional cheat before trusting proof-completion docs.
- Do not retry tactics when the needed change is a maintainer-approved helper, boundary lemma, induction/suspension interface, or oracle replanning.

### What Went Wrong
- The maintainer-approved direct branch-by-branch static ExtCall attempt was still not straightforward: after the projection mismatch was fixed, the success branch required broad generated-prefix simplification of driver_ih and timed out.
- The PLAN temporarily mixed a blocked static stop-state with downstream ready leaves; after reviewed carry-forward closures, plan_oracle replaced C0 with a task-level blocked gate.
- STATE had previously lagged behind accepted E0153/E0154/E0155 and the final blocked-plan replacement; this session committed the tracked PLAN/STATE/LEARNINGS update as 9eb1b922d.
- holbuild cannot currently be used as a source verification step because the structured PLAN correctly blocks builds while high-risk C0 blockers have no low-risk frontier.

### Ignored Signals
- The explicit cheat in Expr_Call_ExtCall_result_static means proof-integrity completion cannot be claimed, even if a previous holbuild succeeded on the intentional-cheat baseline.
- No scheduled frontier with high-risk ancestors is a terminal planning/blocked-state signal, not a reason to choose unscheduled ready components manually.
- Untracked LEARNINGS_type_system_rewrite.legacy.md and tmp_helper.txt repeatedly appear in status and must remain unstaged.
- The task instruction says to stop if the proof/design is not straightforward; this governs the outcome more than the existence of downstream ready-looking components.

### Strategy Adjustments
- Next session should not do proof work unless the user/maintainer explicitly changes the task contract or approves a new static ExtCall proof architecture.
- If resumed under a new architecture, first call plan_oracle to replace/decompose the blocked static ExtCall gate; do not locally redesign or jump to downstream components.
- Keep commits small and unsigned with git commit --no-gpg-sign; stage only relevant tracked files under semantics/prop, never git add -A.
- Treat prior holbuild success as success on an intentional-cheat baseline, not proof completion.
- Current git status after commit 9eb1b922d has only the known untracked legacy/tmp files.

### Oracle Feedback
- Held: Strategist accepted E0155 and confirmed the static ExtCall source is intentionally cheated, no stale partial proof remains, and downstream nonstatic ExtCall is not authorized.
- Held: Final strategist replacement reclassified C0 as a blocked_task_gate because zero reachable cheats is required and the static ExtCall cheat remains.
- Held: Accepted evidence E0144/E0149/E0150/E0155 is a proof-architecture stop, not a mathematical falsehood; end outcome should be blocked, not complete/unprovable.
- Missed earlier reality: the plan previously left ready downstream leaves despite the required static gate being blocked; the final plan_oracle call corrected this by invalidating stale downstream leaves.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3159_t003 - current query_plan: high-risk C0 blockers, no scheduled frontier, no beginable component, no Oracle next
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3152_t002 - holbuild is blocked by structured PLAN risk gate under current state
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3156_t001 - committed tracked task-memory blocked-plan update as 9eb1b922d with --no-gpg-sign
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3159_t002 - current git status: only known untracked legacy/tmp files remain
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3147_t001 - final strategist replacement: C0 blocked_task_gate; no further proof work authorized until new architecture/scope
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3138_t001 - source audit: static ExtCall Resume remains explicit cheat at vyperTypeStmtSoundnessScript.sml:17638-17640
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3137_t004 - previous holbuild succeeded only on intentional-cheat baseline
- episode:E0149 - direct branch-by-branch attempt closed stuck/risk_mismatch after forbidden generated-prefix simplification timed out
- episode:E0155 - accepted stop-state carry-forward closure with source/build/status audit
