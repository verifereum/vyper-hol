# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.2.1
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit/build/proof-search. Current PLAN has Risk-5 C0.2.1 design_blocker_report and no scheduled frontier. Resume only by obtaining operator/maintainer-approved new proof architecture inside `semantics/prop` (or a PLAN replacement after such input) that exposes the optional-driver IH as a compact post-success-continuation fact; otherwise report/keep blocked.
- expected_goal_shape: Blocked static/nonstatic ExtCall optional-driver success tail. The stable source baseline builds only with intentional cheats: `Expr_Call_ExtCall_result_static` uses `pop_last_assum` quarantine and has a success-tail cheat; the captured `driver_ih` is a huge full-prefix implication if consumed, and `extcall_success_continuation_sound_cond_driver_ih` mismatched the current split/conjunctive tail, leaving `state_well_typed st'` / MATCH_MP_TAC No match.
- verify_with: No holbuild until a new authorized proof interface exists. If explicitly authorized for a restoration/doc checkpoint, use holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300).

## If This Fails
- If a future authorized redesign again needs broad `simp`/`gvs`/`AllCaseEqs`, a long generated-prefix adapter theorem, or direct full-prefix `driver_ih` plumbing, checkpoint/close as risk_mismatch and stop per task clarification; do not tactic-search.

## Do Not Retry
- Begin/edit/build any old C0.2.1 descendant (including C0.2.1.1.2, C0.2.1.1.3, or C0.2.1.2) under the current PLAN.: C0.2.1 has been replaced by a Risk-5 design_blocker_report; no scheduled frontier or beginable component exists. Old ready descendants are superseded/stale because they relied on the invalidated optional-driver interface.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2611_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2612_t001
- Direct `irule driver_ih`, `match_mp_tac driver_ih`, `drule_all driver_ih`, or `mp_tac driver_ih` against the current compact success-tail/driver premise.: Checked attempts failed to match or kept the huge full-prefix implication; repeating is tactic thrashing and violates the stop-on-design-issues instruction.
  - evidence: episode:E0114
  - evidence: episode:E0116
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2551_t001
- Use broad `simp[]`/`gvs[]`/`AllCaseEqs()` or case cleanup while the raw generated full-prefix IH is live in assumptions.: This caused timeouts and >4KiB goals; maintainer clarification forbids broad generated-prefix cleanup for this proof.
  - evidence: episode:E0111
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2496_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2498_t001
- Add a long generated-prefix adapter theorem or manually reconstruct the whole ExtCall prefix to bridge to the optional-driver IH.: This is exactly the proof-interface smell/forbidden architecture identified by the maintainer clarification and by E0109/E0116 evidence.
  - evidence: episode:E0109
  - evidence: episode:E0116
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2611_t001
- Assume `extcall_success_continuation_sound_cond_driver_ih` is usable in the current split goal if only the driver premise is solved.: Even with the driver premise cheated, the helper failed to align and left a `state_well_typed st'` / MATCH_MP_TAC No match shape; it must be redesigned or applied to a different unsplit boundary.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2594_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach still unresolved: change the mutual theorem/suspension/finalisation boundary so the optional-driver IH is generated at the post-`run_ext_call`/post-update continuation rather than carried as a full ExtCall-prefix implication.
- We may be optimizing the wrong helper: `extcall_success_continuation_sound_cond_driver_ih` looked compact but failed against the current already-split tail even when its driver premise was cheated. A fresh expert should first question the suspension boundary, not the tactic.
- The PLAN decomposition is now intentionally non-executable: C0.2.1 is a Risk-5 `design_blocker_report`, no frontier. Old ready descendants are stale because they depended on the invalidated optional-driver interface.
- A future design should be de-risked by a tiny probe that applies the new boundary to the unsplit success-tail goal before any full prefix skeleton is copied.

### What Went Wrong
- The quarantine insight was only half the proof. `pop_last_assum` removes the generated IH from prefix/error simplification and those branches build with a tail cheat, but the success tail still requires consuming that same IH in a form that matches the local continuation.
- Direct `irule`/`match_mp_tac driver_ih`, branch-local `drule_all driver_ih`, and `mp_tac driver_ih` with narrow monadic rewrites all failed to reduce the full-prefix generated theorem to a small obligation.
- The compact success-continuation helper did not align with the current split/conjunctive goal even with the driver premise cheated, showing the problem is not merely one missing premise but a proof-interface mismatch.
- The task expected the proof to be straightforward and said to stop on design/plan issues; repeated large-prefix/mismatch evidence triggered the stop condition.

### Ignored Signals
- Earlier >4KiB/full-prefix goals and timeouts were strong evidence that any local generated-prefix specialization would recreate forbidden adapter plumbing; this was underweighted until E0116 confirmed it.
- A build-clean state with success-tail `cheat` validates only static prefix/error branch splitting, not the optional-driver success-tail interface.
- Old ready downstream leaves under C0.2.1 depended on the same optional-driver boundary and should not be treated as independent proof work while the ancestor is Risk 5.

### Strategy Adjustments
- Do not call `begin_component`, edit, or build while query_plan has no frontier. The only useful next action is operator/design input or a replacement PLAN based on a genuinely new interface.
- Require any new plan to prove/apply a tiny post-success-continuation boundary first, in the unsplit tail goal, without broad assumption simplification or generated-prefix adapters.
- Preserve the stable cheated baseline and diagnostic `pop_last_assum` quarantine evidence; do not delete or rewrite it unless the whole proof boundary is replaced.
- Keep all future edits under `semantics/prop`; do not change evaluator/semantics definitions unless the task contract is explicitly changed.

### Oracle Feedback
- Held: the strategist repair after E0111 correctly identified quarantining the raw generated IH via `pop_last_assum`; E0113 validated this for prefix/error branches with a success-tail cheat.
- Missed: the compact-premise plan assumed direct matching from `driver_ih`; E0114 showed `irule`/`match_mp_tac` do not match the generated full-prefix theorem to the compact driver premise.
- Missed again: branch-local native specialization remained non-straightforward; E0116 showed it still exposes/requires the huge full-prefix implication and the helper itself mismatches the split goal.
- Current oracle result: C0.2.1 was replaced by a Risk-5 design_blocker_report with no executable frontier; old C0.2.1 descendants are superseded/stale.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2611_t001 - strategist replacement: C0.2.1 accepted as Risk-5 design_blocker_report, no proof edits authorized
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2612_t001 - current query_plan: high-risk C0/C0.2/C0.2.1/C0.2.1.1, no scheduled frontier, no beginable component
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2614_t003 - handoff-time query_plan confirms no frontier remains
- episode:E0116 - terminal risk_mismatch for local C0.2.1.1.2 replacement: static prefix builds with cheat, success tail blocked
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2574_t001 - success-tail probe: captured generated driver theorem remains a huge full-prefix implication
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2581_t001 - `drule_all driver_ih` specialization failed/no small obligation
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2585_t001 - `mp_tac driver_ih` plus narrow rewrites still left large full-prefix implication
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2594_t001 - `extcall_success_continuation_sound_cond_driver_ih` failed to align even with driver premise cheated
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2596_t001 - source restored to build-clean partial skeleton with success-tail cheat
