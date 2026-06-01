# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0
- status: blocked
- active_file: semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md
- next_action: Do not attempt proof edits/builds under the current PLAN. The accepted C0.1 stop/report state has no scheduled frontier; resume only if a maintainer/operator supplies a replacement proof-boundary/induction-suspend plan for ExtCall or explicitly authorizes new proof-architecture work. If such instruction arrives, first call plan_oracle with E0070/E0071 evidence before editing.
- expected_goal_shape: Under the old `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` boundary, after splitting `eval_exprs cx es st` the live goal still contains a >4KiB generated optional-driver prefix spanning eval_exprs/check/lift_option/build_ext_calldata/run_ext_call/update_accounts/update_transient; local `simp[]` and `gvs[no_type_error_result_def]` time out before concrete success branches are isolated.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300) only verifies the restored intentional-cheat baseline; it is not proof completion.

## If This Fails
- If a future replacement plan still exposes the same generated-prefix goal or requires broad prefix cleanup/manual generated-prefix adapters, close/checkpoint the active component as stuck/risk_mismatch and escalate; do not try simplifier variants.

## Do Not Retry
- Inline-under-TRY boundary movement in the mutual theorem skeleton.: E0068 showed matchers interact with neighboring Call/Send goals or leave the same generated-prefix goal; not mechanically stable.
  - evidence: episode:E0068
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1576_t001
- Focused Resume shell with routine `simp[]`/`gvs[]` after splitting `eval_exprs`/`args_res`.: E0070 showed the generated optional-driver prefix remains live; local simplification times out before concrete success branches.
  - evidence: episode:E0070
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1595_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1599_t001
- Direct `irule extcall_expr_sound_from_generated_ih` or tiny `well_typed_expr_def` cleanup before it.: C0.1/E0066 showed no match against the live Resume goal and even one-step typing cleanup timed out under the generated prefix.
  - evidence: episode:E0066
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1489_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1491_t001
- Broad `simp`/`gvs`/`AllCaseEqs()` or long generated-prefix adapter/witness theorem to recover the optional-driver premise.: Forbidden by maintainer clarification and repeatedly observed as the proof-interface smell causing >4KiB goals/timeouts; would be new proof architecture, not the stopped straightforward path.
  - evidence: episode:E0067
  - evidence: episode:E0070
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1508_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not yet implemented: change the induction/suspend/proof boundary so the optional-driver IH is consumed before it becomes a full ExtCall monadic success-prefix implication, or prove a genuinely small source-level continuation theorem whose live matching is validated first.
- We may have been optimizing the wrong boundary rather than the theorem itself: both inline-under-TRY and focused-Resume attempts leave the same generated-prefix artifact.
- The current replacement PLAN is a stop/report abstraction, not a proof-completion abstraction. It is right for the task's stop condition, but not sufficient to prove ExtCall.
- Do not retry tactics when the actual need is a boundary lemma/suspend redesign/induction interface change. The repeated >4KiB goal is a design signal.
- A fresh expert should first ask: where is the optional driver recursive call introduced by the evaluator/mutual induction, and can the proof be suspended or factored before the generated prefix is reified?

### What Went Wrong
- C0.2.2 assumed the focused Resume would avoid constructor-selection instability and make prefix error cases mechanical. E0070 falsified that: after the eval_exprs split, even the eval_exprs IH discharge and args_res error branch were polluted by the generated optional-driver prefix.
- Direct `simp[]` at the eval_exprs IH timed out; explicit `impl_tac` only moved the failure to `gvs[no_type_error_result_def]` after `Cases_on args_res`; a FAIL probe confirmed the full generated prefix remained.
- Source was restored to the intentional ExtCall cheat baseline, then C0.1 recorded the blockage in TYPE_SYSTEM_REWRITE_PLAN.md. Strategist accepted E0071, and commit 9962ff830 records the report/memory update unsigned.

### Ignored Signals
- Earlier E0067 already showed branch-by-branch work inside the whole Resume boundary left the generated prefix live; the later C0.2.2 plan underweighted that evidence and treated constructor selection as the main blocker.
- The first simplifier timeout on what should have been a small eval_exprs IH premise was a strong stop signal; continuing with local cleanup variants would violate the task's straightforward-proof condition.
- Build success here is only build-clean-with-cheat. It should not be interpreted as proof progress or completion.

### Strategy Adjustments
- Any future proof attempt must begin with a strategist-designed boundary change and a small live matchability probe, not with another proof prefix under the current Resume.
- Require proof-boundary validation before helper investment: show `irule`/`drule_all` or a tiny probe can consume the intended IH/premise without reconstructing generated-prefix witnesses.
- Keep `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` and `semantics/prop/tmp_helper.txt` untracked/unstaged unless an operator explicitly asks to clean them.
- If operator wants continued work despite the stop report, call plan_oracle with E0070/E0071 and request a replacement proof architecture; do not self-redesign.

### Oracle Feedback
- Held: strategist correctly accepted C0.1/E0071 as a reporting/bookkeeping component and blocked further proof work under the task stop condition.
- Missed earlier: strategist's C0.2.2 focused Resume plan assumed the generated-prefix problem would disappear once constructor selection ambiguity was removed; E0070 showed it persists independently.
- Current PLAN reality: no high-risk components, no scheduled frontier, no active component; the only meaningful next step is external replacement-plan input or operator decision, not proof execution.

## Evidence Pointers
- episode:E0070 - focused Resume shell closed stuck/risk_mismatch because generated prefix remained after eval_exprs split
- episode:E0071 - stop/report component proved and accepted
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1595_t001 - `simp[]` at eval_exprs IH timed out under generated prefix
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1599_t001 - `gvs[no_type_error_result_def]` after args_res split timed out under generated prefix
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1601_t001 - FAIL probe confirmed full generated prefix remains
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1616_t003 - restored `vyperTypeStmtSoundnessTheory` builds on intentional-cheat baseline
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1624_t001 - strategist accepted C0.1 report
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1630_t001 - unsigned commit `9962ff830 Report ExtCall proof architecture blockage`
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1631_t001 - final git status has only untracked scratch/legacy files
