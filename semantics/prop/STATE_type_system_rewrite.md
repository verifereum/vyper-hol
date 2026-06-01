# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.2.1.4.1
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First call plan_oracle(mode='review', component_id='C0.2.1.4.1', evidence_ids=['TO_type_system_rewrite-20260601T220715Z_m2892_t001'], planning_reason='review closed episode E0137'). If accepted, begin the scheduled next component, currently C0.2.1.4.2, and prove `extcall_nonstatic_projected_state_well_typed[local]` near the ExtCall helper block.
- expected_goal_shape: Pending strategist review, then C0.2.1.4.2 boundary lemma: compact assumptions for nonstatic ExtCall successful `eval_exprs`, `MAP expr_type es = BaseT AddressT::BaseT (UintT 256)::arg_types`, compact optional-driver IH, conclusion `state_well_typed st'`. It should mirror `extcall_static_projected_state_well_typed` without the generated Resume prefix in context.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)

## If This Fails
- If the boundary lemma proof fails only in routine prefix cases, inspect holbuild goal and adjust locally. If it again requires broad generated-prefix simplification, a generated-prefix adapter theorem, or simplifying the Resume with the driver prefix visible, close/checkpoint the active component as risk_mismatch and call plan_oracle review; do not continue tactic search.

## Do Not Retry
- Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]` by unfolding/splitting the whole nonstatic ExtCall evaluator with generated `driver_ih` visible.: E0136 showed even local prefix simplification timed out when the generated optional-driver prefix remained in context; the oracle replaced this with a projected boundary lemma strategy.
  - evidence: episode:E0136
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2884_t001
- Assert `returnData = [] /\ IS_SOME drv ==> ...` in the Resume using `mp_tac driver_ih >> simp[...]`.: E0135 timed out; the generated prefix is still too large even after branch-local splitting.
  - evidence: episode:E0135
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2869_t001
- Inline the proof of `vs <> [] /\ TL vs <> []` from `exprs_runtime_typed_def` inside the Resume.: This small fact timed out in the polluted Resume context; use the kept helper `extcall_nonstatic_args_runtime_typed_nonempty` instead.
  - evidence: episode:E0136
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2879_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m2892_t001
- Apply `extcall_static_projected_state_well_typed` or any projected helper at the top of a generated Resume to bridge an unconditional compact IH from the full generated prefix.: Earlier E0133 showed direct top-level helper consumption does not match the generated guarded IH and leads to timeouts/forbidden prefix plumbing.
  - evidence: episode:E0133
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2812_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m2819_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach now selected by the oracle: stop trying to prove the nonstatic Resume directly; factor a projected-state boundary lemma outside the generated Resume context, analogous to the static helper.
- A fresh expert should question why nonstatic work is still scheduled while the static Resume success cheat remains queued; however query_plan currently requires review of E0137 before any new begin and then schedules C0.2.1.4.2.
- The wrong optimization was trying to consume the generated optional-driver IH inside the Resume while it polluted simplification. The right abstraction is a compact boundary lemma with an explicit driver-IH premise.
- Do not keep retrying local simp/gvs variants in the Resume. If the next proof gets hard, the boundary lemma statement likely needs adjustment, not another tactic.

### What Went Wrong
- C0.2.2/E0134: linear nonstatic prefix splitting reached the success tail, but helper interfaces did not mechanically consume the generated optional-driver IH; source was reverted to the cheated baseline.
- C0.2.1.4/E0135: the oracle-recommended conditional premise `returnData = [] /\ IS_SOME drv ==> ...` using `mp_tac driver_ih >> simp[...]` timed out, showing the generated prefix still polluted simplification.
- C0.2.1.4.1/E0136: the direct `extcall_success_continuation_sound` Resume route also timed out with the generated driver IH visible; even small local prefix `gvs[return_def, raise_def]` after calldata split became too large.
- One stable source improvement was kept and proved: `extcall_nonstatic_args_runtime_typed_nonempty[local]`, verified by holbuild in E0137.

### Ignored Signals
- The >4KiB holbuild goals with the full generated optional-driver prefix were design signals, not ordinary tactic failures.
- The old helper proof around `extcall_static_projected_state_well_typed` already showed that doing ExtCall prefix reasoning in a compact theorem is safer than inside a generated Resume.
- The stale STATE file still points at old C0.2.2 scheduling; trust query_plan/DOSSIER over that text until save_handoff rewrites it.

### Strategy Adjustments
- Next session must not edit/build before the required plan_oracle review of proved E0137.
- After review acceptance, prove C0.2.1.4.2: add `extcall_nonstatic_projected_state_well_typed[local]` near the static projected helper, using compact assumptions and the already-proved nonstatic nonempty helper.
- In the boundary lemma, copy the static helper structure but use `extcall_nonstatic_args_runtime_typed_dest`, `extcall_nonstatic_args_runtime_typed_nonempty`, `run_ext_call_accounts_well_typed`, and `extcall_success_continuation_state_well_typed`.
- Only after C0.2.1.4.2 builds should C0.2.1.4.3 shorten the Resume to call the boundary lemma; do not unfold the whole nonstatic evaluator in the Resume.

### Oracle Feedback
- Held: E0136 confirmed the oracle's later diagnosis that direct Resume proof is the wrong abstraction under generated-prefix pollution.
- Missed: the E0135 conditional-driver-premise repair was still too risky; the suggested `mp_tac driver_ih >> simp[...]` timed out.
- Current oracle repair after E0136: keep the nonempty helper, prove a nonstatic projected-state boundary lemma outside the Resume, then use it in a small Resume consumer.
- Query_plan now reports no beginable component until E0137 is reviewed; Oracle next after review is C0.2.1.4.2.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2897_t003 - current gate: pending strategist review of E0137, Oracle next C0.2.1.4.2 after review
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2892_t001 - target build clean with `extcall_nonstatic_args_runtime_typed_nonempty` kept and nonstatic Resume reverted to cheat
- episode:E0137 - proved/carry-forward audit for nonstatic argument nonempty helper
- episode:E0136 - direct nonstatic Resume proof timed out with generated driver IH visible
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2884_t001 - evidence of timeout at local `gvs[return_def, raise_def]` after calldata split
- episode:E0135 - conditional driver premise assertion timed out
- tool_output:TO_type_system_rewrite-20260601T220715Z_m2869_t001 - evidence of timeout for `mp_tac driver_ih >> simp[...]` conditional premise
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml - `extcall_nonstatic_args_runtime_typed_nonempty[local]` near the ExtCall helper block; nonstatic Resume still contains intentional `cheat`
