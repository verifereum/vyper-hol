# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.4.3.a
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First call plan_oracle(mode='review', component_id='C0.4.3.a', evidence_ids=['TO_type_system_rewrite-20260602T195240Z_m4577_t001','TO_type_system_rewrite-20260602T195240Z_m4577_t003','TO_type_system_rewrite-20260602T195240Z_m4577_t002','TO_type_system_rewrite-20260602T195240Z_m4578_t001'], planning_reason='review closed episode E0244'). If accepted, query_plan; expected next executable leaf is C0.4.3.b or C0.4.3.c depending on strategist scheduling.
- expected_goal_shape: Source now has manual progress in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]` (not a separate `Expr_Call_ExtCall_result_static_success` block): static branch is inlined, `run_ext_call ...` is split, the generated optional-driver premise has been discharged, and the remaining intentional `cheat` is after `strip_tac` around line 17803 in the concrete ExtCall `SOME` tail. `vyperTypeStmtSoundnessTheory` builds with that remaining cheat.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If review rejects E0244, follow updated PLAN. If the next concrete tail proof again exposes generated-prefix obligations before concrete tuple/success facts, checkpoint or close with risk_mismatch evidence; do not use broad `gvs[]`/`AllCaseEqs()` or generated-prefix adapter theorems. If focused build fails outside active obligations, checkpoint_progress with tool_limit evidence and stop.

## Do Not Retry
- Apply `extcall_static_projected_sound` or `extcall_static_projected_state_well_typed` at the outer static ExtCall Resume boundary.: E0233 showed the required unconditional compact driver IH is unavailable there; the live IH is generated-prefix guarded.
  - evidence: episode:E0233
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m4485_t001
- Transcribe the old projected-tail skeleton immediately after `Cases_on run_ext_call` and expect a single concrete `SOME result` branch.: E0232/E0241 showed that old boundary exposes 9 generated-prefix goals before concrete success facts; manual progress has now changed the source boundary instead.
  - evidence: episode:E0232
  - evidence: episode:E0241
  - evidence: tool_output:TO_type_system_rewrite-20260602T125148Z_m4534_t001
- Use broad `gvs[]`, `AllCaseEqs()`, or generated-prefix adapter theorems to mine the optional-driver premise.: Forbidden by task/PLAN and empirically timed out on the large generated-prefix state.
  - evidence: episode:E0241
  - evidence: tool_output:TO_type_system_rewrite-20260602T125148Z_m4553_t001
  - evidence: plan:C0.4.3.a
- Continue using the old `Expr_Call_ExtCall_result_static_success` Resume location as the active source target without checking current source.: Manual commit `eb2633148` inlined/changed the static branch; the remaining cheat is now in `Expr_Call_ExtCall_result_static` around line 17803.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4577_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4577_t002
- Stage or commit `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are pre-existing untracked artifacts unrelated to task-owned proof progress.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4576_t001

## Reflection
### Tunnel Vision Check
- Manual progress changed the proof boundary: the static ExtCall branch is now inlined in `Expr_Call_ExtCall_result_static`; do not assume the old `Expr_Call_ExtCall_result_static_success` Resume still exists.
- Outside-the-box approach that worked: do not force a separate static-success Resume boundary; inline enough of the branch to discharge the generated optional-driver premise before the concrete tail.
- The PLAN decomposition is plausible after E0244, but it may need the strategist to mark C0.4.3.a done and adjust C0.4.3.b/c to the new source shape.
- Fresh expert should first inspect lines 17758--17804 and ask: is the remaining `cheat` purely concrete-tail soundness, or are there still hidden generated-premise obligations?
- Avoid optimizing old projected helpers. The immediate issue is finishing the concrete tail after manual progress, not re-proving `extcall_static_projected_sound`.

### What Went Wrong
- Earlier C0.4.3 assumed the concrete `SOME` tail appeared immediately after `Cases_on run_ext_call`; E0241 showed a large generated optional-driver premise came first.
- I initially retried direct assumption acceptance (`first_assum MATCH_ACCEPT_TAC`) in the old source shape; it failed because the exact source boundary still exposed the generated premise as a separate top goal with noisy assumptions.
- Manual progress in commit `eb2633148` made the actual proof-state boundary better: static branch is inlined and the generated premise is discharged before the remaining tail cheat.

### Ignored Signals
- E0232/E0241 already showed the branch split produced 9 subgoals and a generated-prefix premise; this was a decomposition signal, not a cue to search for stronger simplifiers.
- The user's manual-progress note meant source reality could have superseded STATE/PLAN wording; I checked the source and found the old `Expr_Call_ExtCall_result_static_success` block had indeed been replaced/merged.
- Pre-existing untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` and `semantics/prop/tmp_helper.txt` remain unrelated and must not be staged.

### Strategy Adjustments
- Next session should treat E0244 as the authoritative proof-status update: C0.4.3.a is closed proved pending required strategist review.
- After review, continue only the scheduled leaf. For C0.4.3.c, work at the remaining `cheat` after `strip_tac` in the inlined static branch; do not resurrect the deleted static-success Resume boundary.
- Use focused verification `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)` first; aggregate `vyperSemanticsHolTheory` can be used after a stable source checkpoint.
- If proving the tail, derive account well-typedness via `run_ext_call_accounts_well_typed`, runtime consistency from `env_consistent/state_well_typed/accounts_well_typed` facts, and use `extcall_after_state_update_tail_sound` or the existing local tail helper pattern.

### Oracle Feedback
- Held: strategist's E0241 replacement insight that generated-IH passthrough must precede concrete-tail work was correct; manual progress appears to implement that.
- Missed/source drift: PLAN still mentions `Expr_Call_ExtCall_result_static_success`, but source now inlines the static branch under `Expr_Call_ExtCall_result_static`; strategist review should reconcile wording with source reality.
- Held: maintaining prefix error subresumes remains valid; `Expr_Call_ExtCall_static_run_none` is still present and builds.

## Evidence Pointers
- episode:E0244 - closed C0.4.3.a proved after reviewing manual source progress and focused build
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4577_t001 - read of current static ExtCall source showing inlined branch and remaining tail cheat at line 17803
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4577_t003 - focused `vyperTypeStmtSoundnessTheory` build succeeds with remaining intentional cheat
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4577_t002 - git log shows manual source commit `eb2633148 Make some progress on a cheat`
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4578_t001 - commit stat confirms manual progress only modified `semantics/prop/vyperTypeStmtSoundnessScript.sml`
- episode:E0241 - previous old-boundary C0.4.3 attempt failed with generated-prefix fanout, motivating the replacement plan
