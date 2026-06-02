# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit/build/prove under the current PLAN. query_plan shows C0 done with no frontier/beginable component/Oracle next. If the maintainer/user authorizes fresh ExtCall proof architecture inside semantics/prop or relaxes the generated-prefix restrictions, call plan_oracle(mode="replace", component_id="C0", planning_reason="fresh ExtCall proof architecture after terminal blocked_report", evidence_ids=["TO_type_system_rewrite-20260601T220715Z_m4232_t001","TO_type_system_rewrite-20260601T220715Z_m4241_t001","TO_type_system_rewrite-20260601T220715Z_m4253_t001","TO_type_system_rewrite-20260601T220715Z_m4261_t001","TO_type_system_rewrite-20260601T220715Z_m4270_t001"]) before any begin_component/build/edit.
- expected_goal_shape: No HOL goal should be active. The PLAN is terminal: C0 blocked_report done, no scheduled frontier, no beginable component, no Oracle next. Existing prior holbuild success is only restored intentional-cheat baseline evidence; proof completion is not valid. A build attempted with no active executable component is now rejected by the PLAN gate.
- verify_with: After a new authorized PLAN component exists and begin_component succeeds, first verify the baseline with holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300), then follow that component's verification instructions. Do not build under the current terminal PLAN unless the operator/harness permits a baseline-only check.

## If This Fails
- If plan_oracle/maintainer authorization still produces no low-risk executable frontier, report blocked/design-stop rather than handoff-looping or starting old superseded leaves. If a future authorized proof probe again produces generated-prefix fanout or >4KiB prefix goals before a concrete run_ext_call success continuation, checkpoint or close that authorized component with evidence and escalate; do not solve those fanout goals individually.

## Do Not Retry
- Retry the straight-line `Cases_on run_ext_call` / tuple-result split / `rename1 SOME result` probe at the current static-success Resume boundary.: E0217 already tested this and failed before helper matching with 9 input goals and a huge generated optional-driver prefix; repeating it is tactic thrashing at a bad proof boundary.
  - evidence: episode:E0217
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4232_t001
- Solve the generated-prefix fanout goals individually, or use broad `simp`/`gvs`/`AllCaseEqs()` to mine the optional-driver premise from the top-level generated context.: Maintainer clarification and PLAN forbid generated-prefix reconstruction; prior probes/timeouts show this produces hostile large goals and violates the allowed straightforward proof path.
  - evidence: episode:E0212
  - evidence: episode:E0217
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4165_t001
- Apply `extcall_static_projected_sound` or `extcall_static_projected_state_well_typed` at the top/current Resume boundary as if an unconditional driver IH were available.: Earlier probes showed direct `irule` does not match; explicit specialization requires an unavailable unconditional driver IH and times out on the generated premise.
  - evidence: episode:E0213
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4178_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4188_t001
- Begin old ready-looking C0.3-C0.7 leaves or claim completion because holbuild previously succeeded.: The C0 replacement superseded those leaves. Build success is only for the restored intentional-cheat baseline, and proof-integrity completion is invalid while cheats/obligations remain.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4253_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4255_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4267_t004
- Run holbuild under the current terminal PLAN without first obtaining a new executable component/frontier.: The structured PLAN gate blocks builds when no active component and no executable frontier remain; the latest baseline-build attempt was rejected.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4270_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4272_t003

## Reflection
### Tunnel Vision Check
- Outside-the-box route still not executed: restructure/suspend the mutual proof earlier or later so the optional-driver IH is produced natively inside a compact concrete success-continuation branch, instead of trying to expose it from the current static-success Resume boundary.
- We may be optimizing the wrong boundary, not the wrong tactic: guarded continuation helpers can be semantically right while the current Resume point is too late/too broad and fans out before helper matching.
- The current PLAN decomposition is intentionally terminal, not executable. A fresh expert should first question whether new ancestor-level proof architecture is authorized, not how to patch old C0.3-C0.7 tactics.
- Do not retry branch-splitting when a boundary lemma, suspend/refactor, definition-level proof interface, or oracle/maintainer authorization is needed.
- A fresh expert should ask first whether the task stop condition has already been satisfied: the theorem is neither proved nor shown false, but the allowed straightforward path has been checked and became a design/proof-boundary stop.

### What Went Wrong
- The failed assumption was that a careful linear split at the current static-success Resume boundary would reach one concrete `run_ext_call` SOME/success continuation before helper matching. E0217 showed it produced 9 input goals and a large generated optional-driver prefix before that point.
- Earlier E0212 already showed delayed-equality repair left multiple goals before `run_ext_call`; E0217 confirmed the issue is structural at this proof boundary, not a local rename/case-split issue.
- The optional-driver IH repeatedly appeared guarded by the full monadic ExtCall prefix. Plans or tactics that required an unconditional driver IH did not match the live proof interface.
- The latest session confirmed the terminal state: query_plan has no frontier; the user-requested holbuild check was blocked by the structured PLAN gate because no executable component remains; end_session(blocked) was accepted as the only legal outcome path.

### Ignored Signals
- Multiple prior probes produced >4KiB generated-prefix goals/timeouts whenever broad simplification or prefix recovery was attempted; this should have ruled out another local split sooner.
- Ready-looking old leaves C0.3-C0.7 were under a superseded/invalidated ancestor; scheduler/frontier output, not apparent leaf readiness, is authoritative.
- A clean focused holbuild of vyperTypeStmtSoundnessTheory is only source-restoration evidence while intentional cheats/obligations remain; it is not proof completion.
- The maintainer clarification forbade recovering the driver premise from the top-level generated context by broad simp/gvs/AllCaseEqs or long generated-prefix adapter theorems.

### Strategy Adjustments
- Future proof work must start with a strategist-owned replacement architecture that prevents postcondition-conjunction fanout before `run_ext_call`, or otherwise exposes a compact branch-local optional-driver IH.
- If fresh work is authorized, require the first Risk 1-2 leaf to be a boundary probe demonstrating a single concrete success goal before helper application, not a full proof attempt.
- Keep all edits inside semantics/prop; do not alter evaluator/semantics definitions; do not stage pre-existing untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt` unless explicitly requested.
- Commits must be unsigned; prior terminal tracked updates were committed with --no-gpg-sign as c96fea117. Current git status before handoff showed STATE/LEARNINGS modified by task memory plus the same untracked legacy/temp files.

### Oracle Feedback
- Held: The final C0 replacement correctly treated the evidence as a task stop/report obligation, not semantic unprovability or proof completion.
- Held: The reviewed E0219 closure accepted the task-local report/update and no further proof redesign was attempted without authorization.
- Missed reality earlier: several plans assumed local splitting would reach a guarded-continuation helper-fit point; holbuild evidence showed the current Resume boundary fans out first.
- Current PLAN state is terminal rather than executable: query_plan shows C0 done, no high-risk components, no frontier, no Oracle next; holbuild is blocked under that gate.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4272_t003 - handoff query_plan: C0 done, no frontier/beginable/Oracle next
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4272_t001 - STATE cursor and do-not-retry list reviewed before handoff
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4272_t002 - latest C0 dossier: E0219 terminal report/update, E0217 failed boundary probe, E0218 blocked_report
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4269_t001 - current git status before blocked end-session: task memory modified; legacy/temp files untracked
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4269_t002 - current PLAN gate before blocked end-session: no executable frontier
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4270_t001 - user-requested holbuild check rejected because no PLAN component/frontier remains
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4232_t001 - E0217 exact failure: straight-line run_ext_call/static-success split produced 9 input goals and huge generated prefix before helper fit
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4253_t001 - strategist C0 replacement: terminal stop/report superseding old C0.3-C0.7
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4261_t001 - strategist reviewed/accepted E0219; appropriate terminal outcome is blocked/design-stop
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4255_t001 - prior focused build succeeds only on restored intentional-cheat baseline, not proof completion
- episode:E0217 - failed proof-boundary probe for C0.1.3.1
- episode:E0218 - accepted blocked_report leaf after failed ExtCall boundary
