# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.5.4.1
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First call `plan_oracle(mode='review', component_id='C0.5.4.1', evidence_ids=['TO_type_system_rewrite-20260602T195240Z_m4788_t001','TO_type_system_rewrite-20260602T195240Z_m4792_t003'], planning_reason='review closed episode E0259')`. This review failed once with OracleBudgetExceeded; retry it before any begin_component/build/edit. If accepted, query_plan; expected scheduling should advance through carry-forward C0.5.4.2/C0.5.4.3 toward C0.5.4.4, whose live work is to strengthen the nonstatic success suspend boundary.
- expected_goal_shape: No active HOL goal. Source is stable and focused holbuild was clean with the planned `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]: cheat` still present. query_plan currently blocks all begin_component calls pending strategist review of E0259; after review, C0.5.4.4 should edit the parent `Expr_Call_ExtCall_result_nonstatic` success branch around lines 17962--17968 so the success subresume receives a compact conditional optional-driver IH rather than only the large generated-prefix universal.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If the E0259 review again fails due oracle budget/tooling, do not edit/build; retry review if permitted, otherwise end_session(blocked, blocked_kind='tooling_bug' or 'unknown') with the oracle-budget evidence. If review accepts but schedule points to carry-forward C0.5.4.2/C0.5.4.3, begin and close those carry-forward leaves only as directed; do not reopen their source. If C0.5.4.4 becomes beginable, begin it and modify only the parent nonstatic success suspend boundary, keeping the success subresume cheated until C0.5.4.5.

## Do Not Retry
- Recover the optional-driver IH inside `Expr_Call_ExtCall_nonstatic_success` by moving the large generated-prefix universal and simplifying `check_def`, `lift_option_def`, `get_accounts_def`, `get_transient_storage_def`, `update_accounts_def`, etc.: E0257 showed this recreates the forbidden generated-prefix simplification and times out after 2.5s; the compact IH must be produced at the parent suspend boundary instead.
  - evidence: episode:E0257
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4781_t001
- Apply `drule_all extcall_success_continuation_sound_cond_driver_ih` directly in the current success subresume context without first supplying a compact conditional driver IH and matching tail equation.: The live branch equation is the post-update tail; direct matching failed, and the helper premise requires the optional-driver IH separately.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4772_t001
  - evidence: episode:E0257
- Treat C0.5.5 or C0.5.4.6 audit as complete while `Expr_Call_ExtCall_nonstatic_success` still contains `cheat`.: E0258 showed focused holbuild can be clean only because the planned success obligation remains cheated; audits must wait until C0.5.4.5 removes it.
  - evidence: episode:E0258
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4792_t001
- Stage or commit untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are pre-existing unrelated artifacts and must remain untracked.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4733_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach now validated for error branches: top-level named `suspend` subresumes plus deletion of the generated-prefix universal turns large generated-prefix goals into tiny runtime-error proofs.
- The success branch is different from error branches: deleting the generated-prefix universal is not enough because the optional-driver IH is semantically needed. Optimizing the success subresume tactic is the wrong target; the parent suspend boundary must pass a compact IH.
- The current PLAN decomposition is right after E0258: C0.5.4.4 must be a boundary refactor before C0.5.4.5 proves success. If the schedule drifts to audits or carry-forward leaves, verify dependencies before doing proof edits.
- Do not keep retrying `simp` variations on the success subresume. A fresh expert should first ask: where can the generated optional-driver IH be specialized once, before `suspend`, so the subresume gets a small conditional assumption?

### What Went Wrong
- C0.5.4.2 and C0.5.4.3 succeeded and were committed/reviewed, but C0.5.4.4 exposed a real boundary flaw: the success subresume still received only the large generated-prefix universal for the optional-driver premise.
- Direct `drule_all extcall_success_continuation_sound_cond_driver_ih` did not match the live success-tail equation, and a static-style attempt to simplify the generated-prefix universal inside the success subresume timed out, confirming E0257 risk_mismatch.
- After E0257, the oracle produced the right replacement plan but the structured scheduler briefly made terminal audit C0.5.5 next; E0258 recorded this as plan_incomplete and the oracle repaired dependencies.
- The session then had to process carry-forward C0.5.4.1; closing E0259 was valid bookkeeping, but its required review hit OracleBudgetExceeded, leaving the next session blocked on that review.

### Ignored Signals
- The success branch needs a positive semantic dependency (optional-driver IH), unlike runtime-error branches. Treating it as just another subresume where the generated-prefix universal can be discarded was under-specified.
- The static proof around lines 17808--17816 derives the driver premise before the final tail. That pattern should be moved to the parent nonstatic skeleton, not replayed inside the success subresume.
- A clean focused build with `Expr_Call_ExtCall_nonstatic_success` still cheated is not progress for completion; E0258 confirmed audits must grep for that cheat before accepting build cleanliness.

### Strategy Adjustments
- Next session should not edit source until E0259 review is accepted or the oracle explicitly repairs the pending-review state.
- Once C0.5.4.4 is beginable, work in `Expr_Call_ExtCall_result_nonstatic` near the success split, not initially in the success `Resume` body. The checkpoint passes if after `RESUME_TAC` the success subresume context contains a compact conditional driver IH.
- For C0.5.4.5, only after the compact IH is visible should the success proof apply `run_ext_call_accounts_well_typed`, `runtime_consistent_def`/`env_consistent_get_tenv`, and `extcall_after_state_update_tail_sound_cond_driver_ih`.
- Keep commits narrow and unsigned. Do not stage untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.

### Oracle Feedback
- Held: E0257 review insight was correct: derive/pass compact optional-driver IH at the parent success suspend boundary rather than recovering it in the subresume.
- Held: E0258 review corrected the premature terminal audit schedule; C0.5.5 must wait until C0.5.4.6.
- Missed/tooling: E0259 carry-forward review is still pending because plan_oracle failed with OracleBudgetExceeded, so the next session must clear that administrative gate before proof work.

## Evidence Pointers
- episode:E0255 - C0.5.4.2 calldata-error subresume proved
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4745_t001 - focused build after calldata proof
- episode:E0256 - C0.5.4.3 empty-code/run-none/reverted subresumes proved
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4758_t001 - focused build after three error branches
- episode:E0257 - success subresume stuck/risk_mismatch; optional-driver IH boundary too weak
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4781_t001 - static-style generated-prefix simplification in success subresume timed out
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4783_t001 - source restored to success cheat and focused build clean
- episode:E0258 - premature C0.5.5 audit found remaining nonstatic success cheat
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4794_t001 - oracle repaired plan/dependencies after E0258
- episode:E0259 - carry-forward C0.5.4.1 closed proved, awaiting review
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4798_t001 - E0259 review failed with OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4799_t001 - query_plan shows pending E0259 review as the only allowed next action
