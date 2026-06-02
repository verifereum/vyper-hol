# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.2.2
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Continue active C0.2.2. First inspect the current source around `extcall_expr_sound_from_generated_ih` and `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]`; verify that the Resume is back to `cheat` and that `extcall_expr_sound_from_generated_ih` uses `rewrite_tac[Once well_typed_expr_def]`. Then replace only the static-success Resume cheat with a proof that runs `RESUME_TAC` and closes the first generated optional-driver premise from `TO_type_system_rewrite-20260601T220715Z_m3336_t001`; leave projection goals for C0.2.3 unless they close trivially using placeholders/suspension permitted by the PLAN.
- expected_goal_shape: After `RESUME_TAC`, two goals were observed. Goal 1 is a generated optional-driver premise: a universally quantified ExtCall prefix ending in `returnData = [] /\ IS_SOME drv ==> !env st res st'. ... eval_expr cx (THE drv) st = (res,st') ==> (well_typed_expr env (THE drv) ==> full postcondition) /\ !vt. ...`. Goal 2 is the first projection goal `state_well_typed st'` with ordinary assumptions including `eval_expr cx (Call ret_type (ExtCall T ...)) st = (res,st')`, `eval_exprs cx es st = (INL x,args_st)`, and `exprs_runtime_typed env es x`.
- verify_with: holbuild(targets=['vyperTypeStmtSoundnessTheory'], timeout=300)

## If This Fails
- If the first generated driver-premise goal cannot be closed by stripping the guard, case-analyzing `drv` from `IS_SOME drv`, deriving `well_typed_expr env (THE drv)` from `well_typed_opt env drv`, and specializing the available driver IH, stop and checkpoint/close C0.2.2 with evidence rather than simplifying the ExtCall prefix. If a build fails before the Resume due to `extcall_expr_sound_from_generated_ih`, keep the targeted `rewrite_tac[Once well_typed_expr_def]` fix and avoid reverting to timed-out `simp[Once well_typed_expr_def]`.

## Do Not Retry
- Revert `extcall_expr_sound_from_generated_ih` opening back to `simp[Once well_typed_expr_def]`.: After adding the static projected helper, that `simp` timed out before reaching C0.2.2; the targeted `rewrite_tac[Once well_typed_expr_def]` progressed to the Resume probe.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3333_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3336_t001
- For C0.2.2, simplify or replay the long generated ExtCall prefix (`build_ext_calldata`, account lookup, `run_ext_call`, updates) to recover the optional-driver premise.: The PLAN explicitly forbids this; prior E0108/E0157/E0158 show it is non-straightforward and timeout-prone. C0.2.2 should use only the guard facts `returnData = []` and `IS_SOME drv` plus the driver IH.
  - evidence: episode:E0108
  - evidence: episode:E0157
  - evidence: episode:E0158
- Leave or commit the `FAIL_TAC "c0_2_2_after_resume"` probe in the static success Resume.: It was inspection-only; source was restored to the `cheat` placeholder before handoff. Reintroduce a probe only briefly if the exact goal must be rechecked, then remove it.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3336_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3338_t001
- Stage untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are known pre-existing artifacts outside stable task progress; commits should stage only relevant tracked files under semantics/prop and use `--no-gpg-sign`.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3339_t002

## Reflection
### Tunnel Vision Check
- Outside-the-box approach still worth questioning: instead of proving the generated driver premise inside the same Resume, create a tiny local lemma that consumes `well_typed_opt env drv`, `IS_SOME drv`, and an unconditional driver IH; but do not include the long ExtCall prefix in that lemma statement.
- The PLAN decomposition seems improved for C0.2.1: the semantic boundary helper was the right abstraction. C0.2.2 is now at the exact generated-premise boundary; if it becomes hard, the issue is likely still the Resume proof interface, not an ExtCall evaluator fact.
- Do not optimize the projection proof yet. C0.2.2 is only the optional-driver premise; C0.2.3 owns applying `extcall_static_projected_sound` to projection goals.
- A fresh expert should first ask whether the first RESUME_TAC goal already contains a usable generated expression IH in assumptions, or whether the premise itself is that IH and merely needs a simple proof from the original driver IH in the suspended context.

### What Went Wrong
- C0.2.1 succeeded and was committed as 90cf9f9d0: `extcall_static_projected_sound` is now proved and accepted by strategist review.
- While starting C0.2.2, a probe of the static success Resume was needed. The probe showed the expected two-goal shape, but the probe theorem was restored to `cheat` before handoff because the session ended before proving the premise.
- Adding the new helper changed proof performance earlier in the file: `simp[Once well_typed_expr_def]` in `extcall_expr_sound_from_generated_ih` timed out, while the more targeted `rewrite_tac[Once well_typed_expr_def]` reached the C0.2.2 Resume probe.

### Ignored Signals
- The timeout in `extcall_expr_sound_from_generated_ih` was not a semantic failure; it was a simplifier-scope problem. Broad `simp` on a large context can become unstable after adding helpers, even when a one-step rewrite is enough.
- The first RESUME_TAC goal is large, but the PLAN permits focusing only on the driver-premise guard facts. Do not read the size as authorization to replay the prefix; it is a signal to ignore the prefix except `returnData = []` and `IS_SOME drv`.
- There is uncommitted partial source after the C0.2.1 commit: `vyperTypeStmtSoundnessScript.sml` plus checkpoint-updated memory files. Do not assume the repo is clean.

### Strategy Adjustments
- Next session should begin from active C0.2.2, not re-begin C0.2.1 or call plan_oracle. Use the checkpoint evidence E0160 and exact goal in `TO_type_system_rewrite-20260601T220715Z_m3336_t001`.
- For C0.2.2, prove the driver premise by pure logical stripping/case analysis on `drv`; no `build_ext_calldata`, account lookup, `run_ext_call`, update, `AllCaseEqs`, or generated-prefix simplification should appear.
- Once C0.2.2 is proved/reviewed, commit only after a clean holbuild; use `git commit --no-gpg-sign` and do not stage `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.
- If the driver IH is not available or matching fails after two focused attempts, checkpoint/close stuck and ask for a smaller premise helper rather than building a long adapter theorem.

### Oracle Feedback
- Held: strategist's C0.2.1 replacement insight was correct; a semantic helper over ordinary evaluator assumptions was provable and accepted.
- Held so far: C0.2.2's expected first goal shape is real; `RESUME_TAC` exposes the guarded optional-driver premise exactly as the PLAN described.
- Still unverified: the PLAN's claim that the driver premise is straightforward from the available driver IH. The next session must confirm this without prefix replay.
- Prior oracle miss remains relevant: old linear prefix strategies are invalidated by E0108/E0157/E0158 and should not be retried.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3320_t001 - C0.2.1 helper build succeeded
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3322_t001 - strategist accepted C0.2.1/E0159 and authorized C0.2.2
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3326_t001 - unsigned commit 90cf9f9d0 saved proved C0.2.1 checkpoint
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3333_t001 - broad `simp[Once well_typed_expr_def]` timed out in `extcall_expr_sound_from_generated_ih`
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3336_t001 - C0.2.2 `RESUME_TAC` probe showing two-goal shape and driver-premise goal
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3340_t001 - nonterminal C0.2.2 checkpoint E0160 recorded
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml - static success Resume restored to `cheat`; `extcall_expr_sound_from_generated_ih` has targeted rewrite_tac change
