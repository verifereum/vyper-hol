# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.4.2
- status: ready
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First call plan_oracle(mode='review', component_id='C0.4.2', evidence_ids=['TO_type_system_rewrite-20260602T125148Z_m4517_t001','TO_type_system_rewrite-20260602T125148Z_m4517_t002','TO_type_system_rewrite-20260602T125148Z_m4517_t003'], planning_reason='review closed episode E0240'). If accepted, begin Oracle-next C0.4.3 and work only on the remaining `SOME result` tail cheat in `Expr_Call_ExtCall_result_static_success`.
- expected_goal_shape: After C0.4.3 begins, expected local source shape is `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]` with calldata/empty-code/run-none subresumes already proved and a single intentional `cheat` after `Cases_on run_ext_call ...` for the `SOME result` branch. The desired proof should split the concrete result tuple, close `success = F` as an assert/runtime-error branch, and use `extcall_success_continuation_sound_cond_driver_ih` in the `success = T` branch with the generated driver IH guarded by `returnData = [] /\ IS_SOME drv`.
- verify_with: holbuild(targets=["vyperSemanticsHolTheory"], timeout=600)

## If This Fails
- If the review rejects E0240, follow the updated PLAN. If the C0.4.3 proof again exposes a many-goal generated optional-driver prefix before concrete `SOME (success,returnData,accounts',tStorage')` facts, stop immediately and close/checkpoint with risk_mismatch evidence; do not use broad generated-prefix simplification or adapter theorems. If holbuild/tooling fails outside active proof obligations, checkpoint_progress with tool_limit evidence and stop.

## Do Not Retry
- Apply `extcall_static_projected_sound` or `extcall_static_projected_state_well_typed` at the outer `Expr_Call_ExtCall_result_static` Resume boundary.: E0233 showed the required unconditional compact driver IH is unavailable there; the live IH is generated-prefix guarded.
  - evidence: episode:E0233
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4485_t001
- Transcribe the old `extcall_static_projected_sound` tail immediately after `Cases_on run_ext_call ...` and expect `(do _ od) args_st = (res,st')` in the top goal.: E0232 showed that path exposes 9 generated-prefix goals before concrete success facts; it is the forbidden boundary/fanout path.
  - evidence: episode:E0232
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4464_t001
- Use broad `simp`/`gvs`/`AllCaseEqs()` or a long generated-prefix adapter theorem to mine the optional-driver premise.: Maintainer clarification and current PLAN forbid generated-prefix mining/adapters; if helper application requires this, close/escalate as proof-interface mismatch.
  - evidence: episode:E0232
  - evidence: episode:E0233
  - evidence: plan:C0.4
- Proceed to C0.5/C0.6 before C0.4.3/C0.4.4 close static ExtCall.: Static ExtCall remains the scheduled blocker; C0.5+ are queued downstream and should wait until the static success tail and cleanup are done/reviewed.
  - evidence: tool_output:TO_type_system_rewrite-20260602T125148Z_m4519_t003
- Stage or commit `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are pre-existing untracked artifacts unrelated to task-owned proof progress.
  - evidence: tool_output:TO_type_system_rewrite-20260602T125148Z_m4513_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach now authorized but not yet executed: consume the generated optional-driver IH exactly inside the branch-local concrete success tail, not by trying to create an unconditional driver theorem or applying the old projected helper at the outer branch.
- Do not optimize the old `extcall_static_projected_sound` consumer interface; E0233 proved it mismatches the mutual Resume boundary. The right abstraction for next work is the conditional tail helper `extcall_success_continuation_sound_cond_driver_ih`.
- PLAN decomposition is currently plausible again: C0.4.1 audited the helper/prefix, C0.4.2 confirmed prefix error subresumes are already proved, and C0.4.3 owns only the concrete success/revert tail.
- If C0.4.3 needs copied/generated prefix assumptions in bulk, that is a helper-boundary smell, not a tactic challenge. Escalate rather than building a long adapter.
- A fresh expert should first inspect the exact assumptions at the `SOME result` branch and ask whether the generated driver IH antecedent can be discharged from live branch facts without broad `gvs` or `AllCaseEqs()`.

### What Went Wrong
- Earlier replacement strategy tried applying `extcall_static_projected_sound` at the outer `Expr_Call_ExtCall_result_static` boundary; E0233 showed the live driver IH was still a generated prefix implication, not the compact unconditional premise the helper needs.
- Multiple sessions were blocked by API holbuild tactic-timeout issues in unrelated dependencies; these are now resolved by dependency proof edits, and `vyperSemanticsHolTheory` builds through the API.
- C0.4.2 in this session was audit/proof-status work, not a source edit: the three static prefix error subresumes were already proved in the restored baseline, while the static `SOME result` tail cheat remains for C0.4.3.

### Ignored Signals
- The earlier E0232 failure already showed the inner `run_ext_call` split could fan out into generated-prefix obligations; the current PLAN addresses this by only proving error subresumes first and leaving the concrete success tail to a conditional-IH strategy.
- Do not ignore the maintainer restriction against broad generated-prefix mining: even if a simplifier variant seems tempting, it would violate both PLAN and task clarification.
- Git status includes only task memory changes plus pre-existing untracked artifacts; do not stage `LEARNINGS_type_system_rewrite.legacy.md` or `tmp_helper.txt`.

### Strategy Adjustments
- Next session must review E0240 with the strategist before beginning C0.4.3; query_plan says no beginable component until that review.
- For C0.4.3, work branch-locally in `Expr_Call_ExtCall_result_static_success`; close `success = F` immediately, then for `success = T` derive `accounts_well_typed accounts'` via `run_ext_call_accounts_well_typed` and `runtime_consistent env cx args_st` from current facts before applying `extcall_success_continuation_sound_cond_driver_ih`.
- Use `holbuild(targets=["vyperSemanticsHolTheory"], timeout=600)` for verification; it succeeded after tooling/dependency fixes.
- After reviewed stable progress, inspect diff/status and commit only relevant tracked task-owned memory/source progress unsigned; never `git add -A`.

### Oracle Feedback
- Held: strategist review after E0233 correctly replaced the invalid outer projected-helper plan with the branch-local conditional-driver tail plan.
- Held: C0.4.1 audit plan prevented re-entering the failed outer-boundary strategy and verified the helper/prefix before new proof edits.
- Held: C0.4.2 was low-risk because source already had proved static prefix error subresumes; E0240 captured that only the `SOME result` tail remains.
- Still pending: E0240 has not yet received the required plan_oracle review because handoff interrupted immediately after closing it.

## Evidence Pointers
- episode:E0233 - outer projected-helper strategy failed; driver IH remained generated-prefix guarded at outer static Resume
- tool_output:TO_type_system_rewrite-20260601T220715Z_m4485_t001 - exact FAIL probe showing generated prefix IH at outer static boundary
- episode:E0239 - C0.4.1 audit proved/reviewed; helper and prefix restored and aggregate build succeeded
- tool_output:TO_type_system_rewrite-20260602T125148Z_m4513_t003 - `vyperSemanticsHolTheory` build succeeded after tooling fixes
- episode:E0240 - C0.4.2 closed proved; static calldata/empty-code/run-none subresumes already proved, success-tail cheat remains for C0.4.3
- tool_output:TO_type_system_rewrite-20260602T125148Z_m4517_t001 - read of static ExtCall area showing prefix error subresumes and remaining success-tail cheat
- tool_output:TO_type_system_rewrite-20260602T125148Z_m4517_t003 - aggregate build succeeded for C0.4.2 baseline
- tool_output:TO_type_system_rewrite-20260602T125148Z_m4519_t003 - query_plan after E0240: next required action is plan_oracle review for C0.4.2, then C0.4.3
