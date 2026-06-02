# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit/build/prove. First try plan_oracle(mode="replace", component_id="C0") to repair terminal status for the completed controlled blocked-report subtree, or add a final beginable bookkeeping leaf. Current PLAN has C0.1/C0.2 done, no frontier/beginable/Oracle-next, but parent C0 still shows ready; previous replace call failed only because OracleBudgetExceeded.
- expected_goal_shape: No HOL proof goal should be pursued. Residual cheats intentionally remain at static ExtCall success, nonstatic ExtCall result, and RawCallTarget. E0223 shows the current static-success Resume boundary yields 9 goals and a >4KiB generated optional-driver prefix before a compact run_ext_call SOME continuation is usable.
- verify_with: Only if a new authorized audit/status component exists: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300). Do not claim proof completion from this build; it is restored-cheated-baseline evidence only.

## If This Fails
- If plan_oracle status repair is still unavailable/budget-exceeded and query_plan still has no frontier/beginable component, report blocked/design-stop rather than handoff-looping. If any future authorized proof probe again yields generated-prefix fanout before a compact success continuation, checkpoint/close that component with evidence and escalate; do not solve fanout goals individually.

## Do Not Retry
- Retry the current post-`Cases_on run_ext_call` boundary probe in `Expr_Call_ExtCall_result_static_success`.: E0223 retried the current branch point in the narrowest permitted way and still produced 9 input goals plus a >4KiB generated optional-driver prefix before a compact success continuation was usable.
  - evidence: episode:E0223
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4328_t001
  - evidence: episode:E0221
- Solve generated-prefix fanout goals individually, or use broad `simp`/`gvs`/`AllCaseEqs()` over the ExtCall prefix to mine the optional-driver IH.: Maintainer clarification and PLAN forbid generated-prefix reconstruction; prior probes and accepted E0223 show this is the hostile large-goal path.
  - evidence: episode:E0223
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4328_t001
  - evidence: episode:E0217
- Begin old proof-completion leaves for static ExtCall, nonstatic ExtCall, RawCallTarget, or final zero-cheat validation merely because C0 appears ready.: Those leaves depended on a compact static success boundary that E0223 showed absent; current no-frontier state is a PLAN/status repair issue, not proof authorization.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4332_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4358_t002
- Claim completion because `vyperTypeStmtSoundnessTheory` builds.: The build is on the restored intentional-cheat baseline; grep confirms residual cheats remain at three planned sites.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4347_t003
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4347_t001
- Stage or commit `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are pre-existing untracked artifacts unrelated to the tracked task-local blocked-report checkpoints.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4365_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box route not yet executed: ancestor-level refactor/suspend of the mutual proof so the optional-driver IH is generated natively inside a compact concrete ExtCall success branch, rather than extracted from the current static-success Resume boundary.
- We may be optimizing the wrong boundary, not the wrong helper: existing projected helpers can be semantically right while the Resume point remains too late/broad and exposes generated-prefix fanout before helper matching.
- Current structured PLAN is a controlled blocked-report/audit path, not proof completion. A fresh expert should first question whether parent C0 should be marked terminal/blocked-report, not try to patch the proof script.
- Do not retry tactics where the real need is proof-boundary redesign, a compact IH interface, or explicit maintainer relaxation of generated-prefix restrictions.
- Fresh expert question: is the task stop condition already satisfied? The theorem is neither proved nor false, but the permitted straightforward proof path has repeatedly hit the exact design stop condition.

### What Went Wrong
- The replacement C0.1 checkpoint assumed a minimal post-run_ext_call boundary inspection might certify a compact success continuation; E0223 disproved this by reproducing 9 input goals and a >4KiB generated optional-driver prefix.
- The optional-driver IH remains guarded by the full generated ExtCall monadic prefix at the current Resume boundary. Attempts needing a compact/unconditional driver IH mismatch the live proof interface.
- After C0.1/C0.2 were completed and reviewed, parent C0 still displayed as ready with no frontier; direct close failed because no active/beginable component existed, and status-repair plan_oracle replace then hit OracleBudgetExceeded.
- Focused build success is only restoration evidence on an intentional-cheat baseline; grep confirmed residual cheats remain.

### Ignored Signals
- Earlier E0217/E0221 evidence already showed the same >4KiB generated-prefix fanout; the replacement checkpoint was user-driven but still confirmed the same signal.
- Ready-looking downstream leaves are unsafe without the compact static ExtCall boundary; C0.2/C0.3/C0.4 from proof-completion plans are stale under the blocked-report replacement.
- A clean holbuild of vyperTypeStmtSoundnessTheory can coexist with intentional cheats and must never be treated as final proof integrity.
- The maintainer restriction forbids broad simp/gvs/AllCaseEqs or long generated-prefix adapters, exactly the route the live goal invites.

### Strategy Adjustments
- Next session should focus on PLAN/status repair first: parent C0 needs terminal blocked-report status or a final risk-1 bookkeeping leaf; do not reopen proof work.
- If future proof work is explicitly authorized, start with a strategist-owned ancestor-level architecture/probe demonstrating one compact concrete success goal before helper application.
- Keep all edits inside semantics/prop; do not change evaluator/semantics definitions; do not stage pre-existing untracked LEARNINGS_type_system_rewrite.legacy.md or tmp_helper.txt.
- Commits must be unsigned. This session committed e84f7edb5 (E0223 blocked-status update) and 87d337ad6 (Dossier audit closure) with --no-gpg-sign.

### Oracle Feedback
- Held: strategist accepted E0223 as a real C0.1 risk-mismatch/proof-boundary failure and said no downstream C0.2/C0.3 work should start under that decomposition.
- Held: strategist replaced proof-completion leaves with controlled blocked-report leaves C0.1/C0.2; those were completed and reviewed as documentation/audit work.
- Held: C0.2 review accepted that holbuild success plus cheat grep is baseline restoration evidence, not proof completion.
- Missed/tooling issue: after C0.1/C0.2 done, query_plan still shows parent C0 ready with no beginable frontier; plan_oracle replace for terminal status repair failed with OracleBudgetExceeded.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4328_t001 - E0223 exact holbuild failure: 9 goals and >4KiB generated optional-driver prefix after current run_ext_call split
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4330_t001 - source restored and focused target builds on intentional-cheat baseline after E0223 probe
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4332_t001 - strategist accepted E0223 as boundary/risk-mismatch failure
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4345_t001 - strategist accepted C0.1 documentation/status closure E0224
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4347_t003 - C0.2 focused holbuild succeeds on restored cheated baseline
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4347_t001 - grep confirms residual cheats at static ExtCall success, nonstatic ExtCall, RawCallTarget
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4353_t001 - strategist accepted C0.2 audit closure E0225
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4357_t001 - unsigned commit 87d337ad6 recorded Dossier closure after audit
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4358_t002 - query_plan after audit: no frontier/beginable/Oracle-next but C0 still ready
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4359_t001 - direct close_component(C0) failed because no active component
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4362_t001 - plan_oracle replace/status repair failed with OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4365_t001 - final git status only pre-existing untracked legacy/temp files
