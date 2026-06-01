# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.2.1.1.2
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Do not edit first. Build `vyperTypeStmtSoundnessTheory` immediately to verify the current partial `Expr_Call_ExtCall_result_static` proof after the last unbuilt success-tail edit; inspect the first goal/error at the `extcall_success_continuation_sound_cond_driver_ih` application.
- expected_goal_shape: Current source is partial/unverified. Expected failure, if any, is in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` success tail after static prefix split: obligations from `extcall_success_continuation_sound_cond_driver_ih`, especially its compact conditional driver premise `(returnData=[] /\ IS_SOME drv ==> !env0 st0 res0 st0'. ...)`, to be discharged from captured `driver_ih`. Prefix-error cases should already be past the earlier timeout hazard because `driver_ih` is removed with `pop_last_assum`.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)

## If This Fails
- If the failure is a small tail premise, repair locally within C0.2.1.1.2 using captured `driver_ih` and live prefix facts. If it requires manual full-prefix `qspecl_then`/adapter plumbing or reintroducing `extcall_generated_driver_ih`, close/checkpoint as risk_mismatch and call plan_oracle review; do not continue tactic-thrashing. If build succeeds, close C0.2.1.1.2 as proved, call plan_oracle review, then commit stable progress only if tracked diffs are clean/relevant.

## Do Not Retry
- Use broad `qpat_x_assum` patterns to capture the long generated optional-driver IH.: Patterns like `!s'' vs ... . _` and `_ ==> !env0 ...` failed to match the generated assumption; this wastes time and leaves the IH live.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2522_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2525_t001
- Use `first_x_assum` to quarantine the generated optional-driver IH in the static Resume branch.: It timed out/traversed the large generated assumption rather than cheaply removing it. In this goal shape the working selector is `pop_last_assum`.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2527_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2529_t001
- Leave the raw generated IH in assumptions while calling `simp[]`, `gvs[]`, local `Cases_on vs`, or evaluator unfolding.: E0111 showed this reproduces the prefix proof-interface hazard: timeouts and >4KiB goals before the success tail.
  - evidence: episode:E0111
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2496_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2498_t001
- Reintroduce `extcall_generated_driver_ih_def` / `extcall_generated_driver_ih_elim_expr` or build a long adapter theorem.: E0109/E0110 established that generated-prefix adapter route is the wrong abstraction and the artifacts were deliberately deleted; audit confirms they remain absent.
  - evidence: episode:E0109
  - evidence: episode:E0110
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2512_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box not fully tried: change the generated mutual proof/suspension boundary so the driver IH is generated exactly at the success continuation, instead of hauling it as a huge top-level assumption into branch proofs.
- We may still be optimizing around a generated Resume shape that is fundamentally hostile; `pop_last_assum` is a tactic-level quarantine, not a proof-interface theorem.
- The current decomposition is better than the deleted adapter-helper plan, but remains fragile if the success-tail use of `driver_ih` cannot be solved by matching.
- Do not retry broad patterns for selecting the generated IH; selector choice itself matters because traversing/matching that assumption causes timeouts.
- A fresh expert should question first whether `pop_last_assum` is stable across small proof edits and whether the generated assumption is indeed the oldest assumption in static/nonstatic branches.

### What Went Wrong
- Leaving the raw generated optional-driver prefix implication live caused even narrow `simp[]`/`gvs[]`/case cleanup to time out or expose >4KiB goals; this was recorded in E0111.
- Broad `qpat_x_assum` patterns for the generated IH did not match, and `first_x_assum` was too expensive/wrong-shaped for quarantine. `pop_last_assum` was the first selector that actually removed the generated IH and let prefix splitting proceed.
- The last edit replaced the success-tail cheat with a partial `extcall_success_continuation_sound_cond_driver_ih` application but was not built before handoff, so source is not a verified prefix right now.

### Ignored Signals
- The earlier E0111 timeout evidence meant all assumption-selecting tactics should be treated with suspicion; `first_x_assum` confirmed this by timing out.
- The generated prefix assumption appears as goal assumption 0 in outputs but is stored as the oldest assumption for tactic selection; using `pop_last_assum` is non-obvious and should be preserved.
- A successful build with `cheat` at the tail only proves the quarantine/prefix skeleton, not that the tail driver premise interface is acceptable.

### Strategy Adjustments
- Next session should verify immediately, before editing further, because the file contains a partial unbuilt tail proof.
- Keep the generated driver theorem as an ML theorem value (`driver_ih`) throughout prefix splitting; never return it to assumptions until the compact conditional premise subgoal.
- Prefer small boundary lemmas already present (`extcall_static_args_runtime_typed_dest`, `extcall_static_args_runtime_typed_nonempty`, `extcall_success_continuation_sound_cond_driver_ih`) over unfolding `exprs_runtime_typed_def` or broad simplification.
- If `driver_ih` cannot solve the compact conditional premise by `irule`/matching from concrete prefix facts, escalate; do not recreate the deleted generated-prefix adapter.

### Oracle Feedback
- Held: The strategist's E0111 repair insight was correct in part — quarantining/removing the raw generated IH before prefix simplification avoids the observed static-prefix timeouts; `holbuild` succeeded with a tail cheat after `pop_last_assum`.
- Missed/uncertain: The PLAN suggested `qpat_x_assum` and `irule driver_ih`; `qpat_x_assum` did not match, `first_x_assum` timed out, and the `irule driver_ih` tail use remains unverified after the last edit.
- Held: Deleting `extcall_generated_driver_ih` artifacts was stable; audits/builds E0110/E0112 confirmed no references remain.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2537_t003 - current PLAN shows active C0.2.1.1.2 and next action should continue it
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2537_t001 - git status at handoff: modified source plus untracked legacy/tmp files; do not commit partial proof
- episode:E0113 - nonterminal checkpoint recording quarantine progress and current unbuilt tail edit
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2520_t001 - static branch built with `pop_last_assum` quarantine and success-tail cheat, validating prefix splitting
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2522_t001 - broad `qpat_x_assum` failed to match generated IH
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2527_t001 - `first_x_assum` quarantine attempt timed out
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2529_t001 - `pop_last_assum` reached the static success-tail probe
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2536_t001 - source edit replacing tail cheat with partial helper application; not yet built
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2507_t001 - prior reverted baseline build after E0111
- tool_output:TO_type_system_rewrite-20260601T081233Z_m2512_t001 - cleanup audit: no `extcall_generated_driver_ih` references remain
