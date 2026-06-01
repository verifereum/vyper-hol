# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.1.1.2.4
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit/build first. Query PLAN, then perform the only legal unblocking action: retry plan_oracle(mode='review', component_id='C0.1.1.2.4', evidence_ids=['TO_type_system_rewrite-20260601T081233Z_m1427_t001','TO_type_system_rewrite-20260601T081233Z_m1427_t003','TO_type_system_rewrite-20260601T081233Z_m1427_t002','TO_type_system_rewrite-20260601T081233Z_m1427_t004'], planning_reason='review closed episode E0063'). If review again fails with OracleBudgetExceeded while query_plan still has no frontier, report operational planner/oracle-budget blocker; do not prove/redesign locally.
- expected_goal_shape: query_plan shows no scheduled leaf frontier and no beginable component; only allowed action is strategist review of final stop-state audit episode E0063 for C0.1.1.2.4. E0063 evidence says tracked semantics/prop diff was clean before close, ExtCall Resume remains present, invalidated helper absent, and vyperTypeStmtSoundnessTheory builds. The post-E0063 DOSSIER regeneration is likely an uncommitted tracked memory-file diff because review/commit was blocked by OracleBudgetExceeded.
- verify_with: After strategist review accepts E0063: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300), then git status/diff, stage only relevant tracked semantics/prop memory files with git add -u, and commit --no-gpg-sign. Do not stage untracked tmp/legacy files.

## If This Fails
- If plan_oracle review again fails with OracleBudgetExceeded/schema error and query_plan still permits only that review, use end_session(outcome='blocked', blocked_kind='tooling_bug' or 'unknown') with E0063 audit evidence and the oracle failure evidence. If review succeeds and opens a frontier, begin exactly Oracle next; if it accepts the stop-state audit, inspect diff and make the unsigned checkpoint commit if only task-owned tracked progress files changed.

## Do Not Retry
- Manual `qspecl_then`/ordered witness instantiation of `extcall_generated_driver_ih_elim_expr` over the ExtCall generated prefix.: E0055 showed this is exactly the brittle generated-prefix plumbing forbidden by maintainer clarification; it is a proof-interface smell, not a parsing or witness-order issue.
  - evidence: episode:E0055
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1350_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1351_t001
- Use unchanged `drule_all extcall_generated_driver_ih_elim_expr` or direct `irule` and expect live matching to infer all prefix variables.: E0056 tested this exact low-risk probe and direct variant; both failed on a standalone theorem with intended live assumptions/conclusion.
  - evidence: episode:E0056
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1366_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1368_t001
- Resurrect or depend on `extcall_expr_sound_from_generated_driver_ih` as if it exists in source.: The helper was part of the failed E0055 strategy and was removed; greps in E0058/E0063 confirm it is absent. Recreating it would violate the accepted stop-report plan.
  - evidence: episode:E0058
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1382_t002
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t002
- Direct Resume linearization by unfolding `well_typed_expr`/`evaluate_def` or broad `simp`/`gvs`/`AllCaseEqs()` over the ExtCall prefix.: E0051 showed this splits/loses the whole postcondition or creates timeout/huge-goal prefix simplification, and maintainer clarification forbids recovering the driver premise this way.
  - evidence: episode:E0051
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1292_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1298_t001
- Stage untracked `semantics/prop/tmp_helper.txt` or `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md`, or use `git add -A`.: They are unrelated/ad-hoc untracked files; task requires careful staging only and commits must be unsigned. Final audit status still shows only these untracked files.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1382_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach still not considered: change the original suspend/proof boundary so the optional driver IH is captured in compact form before the ExtCall monadic prefix is generated, instead of trying to recover it afterward via generated-prefix eliminators.
- We may still be optimizing the wrong theorem/helper: `extcall_generated_driver_ih_elim_expr` is proved infrastructure but not a usable consumer boundary for the live Resume; a future redesign should question the boundary theorem shape rather than tactic variants.
- The current PLAN decomposition is intentionally a stop-state/audit subtree, not a proof-completion subtree. Do not reinterpret ready sibling components (C0.1.2 etc.) as permission to continue while C0.1.1.2 remains high-risk blocked and review-gated.
- This session did not retry proof tactics; it executed mechanical carry-forward audits. A fresh expert should first ask whether the task contract now requires operator acceptance of an incomplete proof/cheat rather than further proof work.
- Fresh expert question: why is a required-for-completion top-level proof branch allowed to stop with a cheat? The answer is the task instruction says stop if not straightforward; the next action is operator/strategist handling, not autonomous proof repair.

### What Went Wrong
- The final stop-state audit E0063 completed, but its required strategist review failed twice with OracleBudgetExceeded, leaving query_plan with no frontier and a pending review gate.
- Because review did not complete, the stable progress prompt to commit after E0063 could not legally be followed. Before E0063 close, git status/diff had no tracked semantics/prop diff; after close, DOSSIER was regenerated and likely remains uncommitted.
- Earlier problem still governs: live matching of the generated-driver IH eliminator failed (E0056), and the stale helper-based proof path was removed. The source is build-clean only because the ExtCall result Resume remains a cheat.
- Several small audit commits were made unsigned in this session after reviewed carry-forward leaves: skeleton audit, generated-driver infrastructure audit, wrapper-adapter cleanup audit, and stop-report audit. The final E0063 dossier update is not committed due pending review.

### Ignored Signals
- OracleBudgetExceeded had already occurred in the previous session; retrying the final E0063 review was necessary by the PLAN gate but predictably exposed the same operational limit.
- The existence of remaining ready siblings in query_plan can be misleading; high-risk C0.1.1.2 still blocks direct proof progress until the pending review is resolved.
- Grep for `FAIL_TAC` during stop-report audit matched other pre-existing scripts in semantics/prop; this should not be overinterpreted as dirty ExtCall proof state.

### Strategy Adjustments
- Next session should keep actions minimal: query_plan, retry the exact E0063 review, then either commit the accepted final stop-state documentation or report the oracle-budget blocker.
- Do not run broad proof searches or source edits while the only allowed action is a strategist review. The proof state is already audited; the blocker is planner/oracle review, not HOL.
- If review succeeds, inspect git diff carefully before committing. Stage only tracked task-owned memory/progress files under semantics/prop; never use git add -A and never stage `semantics/prop/tmp_helper.txt` or `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md`.
- If a future oracle replaces the stop-state with proof work, require a demonstrated matchable boundary probe before any final ExtCall Resume proof attempt.

### Oracle Feedback
- Held: The oracle's E0058 review replacement correctly removed the stale C0.1.1.2.3.2 proof leaf and converted the subtree to mechanical stop-state audits.
- Held: Reviews for E0059, E0060, E0061, and E0062 accepted the mechanical carry-forward audits with no PLAN changes; the audited source/build facts matched the PLAN.
- Missed/blocked reality: The final E0063 review could not complete due OracleBudgetExceeded, so the PLAN gate remains stuck even though the audit evidence is complete.
- Current binding state: query_plan allows only plan_oracle review for C0.1.1.2.4/E0063; no build/edit/commit should occur until that review succeeds or the session reports a tooling/planner blocker.

## Evidence Pointers
- episode:E0063 - final stop-state audit closed for C0.1.1.2.4; review pending due oracle budget
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t001 - final audit git status: no tracked diff, only known untracked tmp/legacy files
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t003 - final audit git diff --stat under semantics/prop had no tracked output
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t002 - grep: ExtCall Resume present and invalidated helper absent
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1427_t004 - final audit holbuild of vyperTypeStmtSoundnessTheory succeeded
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1428_t001 - close_component recorded E0063 and regenerated DOSSIER
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1429_t001 - first required E0063 plan_oracle review failed OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1431_t001 - second required E0063 plan_oracle review failed OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1430_t001 - query_plan after E0063: no frontier, only allowed action is review E0063
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1433_t004 - handoff inspection confirms same pending-review gate
