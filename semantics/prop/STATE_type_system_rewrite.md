# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md
- next_action: First check whether the user/maintainer supplied a concrete ExtCall proof-interface or suspend-boundary redesign. If yes, call plan_oracle(mode='replace', component_id='C0') before any HOL work. If no redesign is supplied, do not build/edit/prove; report end_session(outcome='blocked', blocked_kind='external_precondition') with query_plan evidence.
- expected_goal_shape: No active HOL goal. Expected query_plan remains: high-risk [C0], C0 Risk 4 BLOCKED, scheduled leaf frontier none, beginable none, Oracle next none. Remaining task-owned obligations include Expr_Call_ExtCall, Expr_Call_RawCallTarget, raw_call_return_type_well_formed, plan/status update, unsigned commit discipline, and final zero-cheat validation, but none are executable while C0 is active.
- verify_with: Only after a replacement PLAN authorizes executable work: first holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=120); final validation holbuild(targets=["vyperSemanticsHolTheory"], timeout=300) with zero reachable fresh-stack CHEAT warnings.

## If This Fails
- If an authorized redesign still exposes the driver IH only behind the generated ExtCall prefix or requires broad generated-prefix simplification, long qspecl_then over generated temporaries, ASSUME-quoted reconstruction, MATCH_MP/ACCEPT_TAC/CONJ plumbing, or an adapter over the full prefix, checkpoint_progress on the active component with exact holbuild evidence or close_component only for a terminal stuck/proved/abandoned outcome, then escalate/re-plan; do not continue tactic search.

## Do Not Retry
- Use asm "driver_ih" mp_tac >> simp[], broad gvs, or broad simplification to recover the compact optional-driver premise from the generated driver IH.: Repeated evidence shows this exposes or times out on the full generated ExtCall prefix; E0029 confirms the C0.1 local boundary still has the same structural problem.
  - evidence: episode:E0029
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0862_t001
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0864_t001
- Manually specialize the generated optional-driver IH with long qspecl_then lists over ExtCall prefix temporaries or rebuild assumptions with ASSUME/MATCH_MP/ACCEPT_TAC/CONJ plumbing.: This is the prohibited generated-prefix reconstruction path and violates the task's straightforward-proof constraint; the current PLAN marks it as the wrong abstraction.
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0886_t001
  - evidence: episode:E0029
- Add another helper/adapter theorem whose assumptions package the full generated ExtCall prefix in order to derive the compact driver premise.: Such adapters reproduce the same proof-interface problem and do not change what the live Resume context exposes; prior tautological/adapter routes were rejected.
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0886_t001
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0526_t001
- Proceed to Expr_Call_RawCallTarget, raw_call_return_type_well_formed, wrapper/final validation, EVAL probes, commits, or holbuild-as-proof-work while C0 is active.: C0 is required-for-completion and blocks all downstream work until an external redesign is supplied and re-planned.
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0886_t001
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0897_t003
- Call plan_oracle again with no new external redesign merely because C0 is blocked.: The strategist already encoded the external-precondition stop gate; absent new maintainer/user redesign, the ordinary action is blocked report, not another redesign request.
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0886_t001
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0897_t003

## Reflection
### Tunnel Vision Check
- Outside-the-box route still needed: change the source/suspend boundary or theorem architecture so the optional driver recursive call is exposed in compact form before the ExtCall evaluator monadic prefix is accumulated.
- Likely wrong optimization target: improving extcall_success_continuation_sound_cond_driver_ih. It is useful only after a compact driver premise exists; the blocker is premise availability in the generated mutual Resume context.
- The current PLAN decomposition is intentionally a high-risk external-precondition stop gate, not a proof roadmap. A low-risk probe requires external redesign approved through plan_oracle replacement.
- Do not retry tactics here. E0029 shows this is a proof-interface/boundary problem, not a missing simp/metis sequence.
- A fresh expert should first question why the driver expression recursive IH is generated under the full ExtCall evaluator prefix and whether the mutual theorem/suspend layout can isolate the driver call as an ordinary compact recursive call.

### What Went Wrong
- The replacement C0.1 assumption failed: moving the proof boundary locally inside the existing Expr_Call_ExtCall Resume did not expose a compact optional-driver premise.
- The first unfold/probe still showed the driver IH as a giant generated prefix implication over eval_exprs, checks/lifts, build_ext_calldata, run_ext_call, update_accounts, and update_transient.
- Continuing the approved split immediately ran into timeouts/failures on basic local simplification (gvs[no_type_error_result_def], simp[], and Cases_on is_static' >> gvs[]), so the Risk-2 rating was wrong, not merely a tactic choice.
- Experimental edits were reverted to the honest ExtCall cheat, and vyperTypeStmtSoundnessTheory builds at the cheated baseline.
- This session performed only startup/blockage assessment. query_plan still shows C0 Risk 4 BLOCKED with no frontier/beginable component, and git status shows only task memory/plan files plus a legacy LEARNINGS file modified/untracked.

### Ignored Signals
- Earlier evidence already warned that generated-prefix adapters were the wrong abstraction; C0.1 confirmed the same shape rather than derisking it.
- A local Resume boundary probe was authorized, but the first visible goal already exceeded 4KiB and contained the forbidden prefix shape; that should be treated as design failure, not a cue for more tactic search.
- The task says the proof should be entirely straightforward and to stop on design/plan issues; once C0.1 failed, downstream RawCallTarget, builtin cleanup, EVAL/build probes, commits, and final validation remain unauthorized.
- Do not interpret query_plan's generic complete option as proof completion; task-owned cheats remain and C0 is required-for-completion but blocked.

### Strategy Adjustments
- Do not start future sessions with holbuild or source edits while C0 remains Risk 4 blocked. First verify query_plan/frontier and whether a concrete external redesign has been supplied.
- If a redesign is supplied, route it through plan_oracle(mode='replace', component_id='C0') so the strategist creates Risk-1/2 children before edits/builds.
- Future work should expose the optional driver IH at a source/suspend boundary instead of recovering it downstream from the generated full ExtCall prefix.
- Keep runtime_consistent_get_tenv and extcall_success_continuation_sound_cond_driver_ih as potentially useful post-run continuation infrastructure, but do not build new helpers around the full generated driver IH.
- Commit discipline remains: all edits under semantics/prop only, and any future commit must use git commit --no-gpg-sign.

### Oracle Feedback
- Held: C0.1 failed as proof-interface evidence, not tactical weakness; plan_oracle review accepted E0029 and replaced the subtree with the C0 external-precondition stop gate.
- Held: generated-prefix adapters and broad generated-prefix simplification are prohibited and wrong for this task's straightforward-proof contract.
- Held: no low-risk executable frontier remains; current query_plan confirms C0 Risk 4 BLOCKED, no scheduled leaf frontier, no beginable component, and no Oracle-next component.
- Missed by prior replacement: the local Resume-boundary probe was still too optimistic; even the branch split did not make the compact premise available without prohibited plumbing.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0897_t003 - current handoff query_plan confirms C0 Risk 4 BLOCKED, no frontier/beginable/oracle-next
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0897_t001 - STATE cursor and do-not-retry list before this handoff
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0897_t002 - dossier summary for C0 including E0029 risk_mismatch and reverted baseline
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0895_t001 - startup git status: only task memory/plan files modified plus legacy LEARNINGS file, no source proof action taken this session
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0895_t002 - startup query_plan confirmed same C0 Risk 4 blocked gate before blocked end_session
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0886_t001 - strategist replacement restoring external-precondition stop gate after E0029
- episode:E0029 - terminal C0.1 risk_mismatch episode: local boundary probe failed and source was reverted
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0862_t001 - first C0.1 probe showed full generated ExtCall prefix guarding driver IH
- tool_output:TO_type_system_rewrite-20260531T201607Z_m0883_t001 - focused baseline build succeeded after reverting experimental edits
