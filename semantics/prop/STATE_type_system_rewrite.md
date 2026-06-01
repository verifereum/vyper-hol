# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.1.1.2.3
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: First remove or replace the temporary probe in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` (currently `rpt gen_tac >> strip_tac >> FAIL_TAC "probe extcall resume initial"` at about lines 17231-17233). Then continue C0.1.1.2.3 by constructing the linear ExtCall Resume proof: split expression/place conjuncts as before, unfold only one evaluator layer, destruct `eval_exprs`, close error cases immediately, and proceed one monadic operation at a time.
- expected_goal_shape: Without removing the probe, holbuild will fail at `FAIL_TAC "probe extcall resume initial"` in `Expr_Call_ExtCall_result`. After replacing it with proof text, expected local proof shape is the ExtCall expression-result conjunct after `rpt gen_tac >> strip_tac`: generated IH assumptions for `eval_exprs` and optional driver are in context, plus `well_typed_expr ... ExtCall ...` and `eval_expr ... = (res,st')`; C0.1.1.2.3 should stop/checkpoint once the proof reaches a single concrete success continuation with target/calldata/accounts/tStorage/run/update facts, before solving the optional-driver IH tail.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300)

## If This Fails
- If failure is only the temporary `FAIL_TAC`, remove/replace it and rebuild. If routine prefix splitting requires broad `gvs`/`AllCaseEqs()` over the whole ExtCall prefix, generated-prefix witness lists, or wrapper-adapter lemmas, checkpoint_progress with the failing goal evidence and close C0.1.1.2.3 as stuck/risk_mismatch if the linear proof is not straightforward.

## Do Not Retry
- Revive static/nonstatic wrapper-adapter lemmas around `extcall_generated_driver_ih_elim_expr`.: E0047 showed direct matching fails and explicit specialization requires brittle generated-prefix witness lists; the strategist invalidated this path.
  - evidence: episode:E0047
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1238_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1250_t001
- Manually instantiate broad generated-prefix eliminators with dozens of `s_*`, `x_*`, and `st_*` witnesses.: This is the exact proof-interface failure the replacement PLAN is avoiding; if it reappears in C0.1.1.2.3/2.4, stop and escalate.
  - evidence: episode:E0047
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1236_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1246_t001
- Use broad `simp`/`gvs` or global `AllCaseEqs()` over the whole ExtCall prefix from the top Resume context.: Prior attempts timed out or produced huge goals; maintainer and PLAN require linear operation-by-operation splitting with immediate error-case closure.
  - evidence: episode:E0039
  - evidence: episode:E0041
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1250_t001
- Commit current tracked source as-is.: A temporary `FAIL_TAC "probe extcall resume initial"` is present in `Expr_Call_ExtCall_result`; remove/replace it and verify before any commit.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1281_t002
  - evidence: source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17231
- Stage untracked `semantics/prop/tmp_helper.txt` or `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md`, or use `git add -A`.: They are unrelated/ad-hoc files noted across sessions; operator explicitly forbids broad staging.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1281_t002
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1216_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach now chosen by the strategist: abandon the wrapper/eliminator abstraction and prove the final ExtCall Resume linearly inside the concrete branch. Do not drift back to optimizing wrapper lemmas.
- Fresh expert should first question the current dirty source: a probe `FAIL_TAC` was inserted at `Expr_Call_ExtCall_result` immediately before handoff and has not been built or removed.
- The PLAN decomposition is still plausible after E0047: C0.1.1.2.3 handles prefix splitting only; C0.1.1.2.4 handles optional-driver IH only after a concrete success branch. Keep that separation.
- Do not optimize the old `extcall_expr_sound_from_generated_ih` theorem or the broad `extcall_generated_driver_ih_elim_expr`; use them only as reference/optional infrastructure, not as the new proof target.
- A fresh expert would inspect the exact generated IH assumptions in the Resume goal before writing tactics, then decide whether the linear proof can consume them without reconstructing internal prefix witnesses.

### What Went Wrong
- The static wrapper component C0.1.1.2.2.1 failed because the broad eliminator still required a long `qspecl_then` list over generated monad state witnesses; direct `irule extcall_generated_driver_ih_elim_expr` did not match the branch-local conclusion. Evidence: episode:E0047 and tool outputs TO_type_system_rewrite-20260601T081233Z_m1236_t001, TO_type_system_rewrite-20260601T081233Z_m1238_t001, TO_type_system_rewrite-20260601T081233Z_m1246_t001.
- The old wrapper abstraction hid the generated IH too late/too low-level: it avoided early simplifier blowups but still forced generated-prefix reconstruction at success tails.
- During C0.1.1.2.3 setup I inserted a `FAIL_TAC` probe in the final Resume but did not build after it because handoff arrived; this leaves a tracked source diff that the next session must handle first.

### Ignored Signals
- The proof-hygiene checkpoint warning about long `qspecl_then` lists applied even inside the planned static wrapper: the wrapper was becoming exactly the brittle generated-prefix plumbing it was supposed to hide.
- The task says to stop if the proof is not straightforward; E0047 was correctly closed, but only after trying both direct matching and explicit witness specialization.
- Untracked `semantics/prop/tmp_helper.txt` and `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` still exist; do not stage them.

### Strategy Adjustments
- Follow the accepted replan from TO_type_system_rewrite-20260601T081233Z_m1250_t001: no static/nonstatic wrapper adapters; perform a careful linear branch proof in `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`.
- For C0.1.1.2.3, use targeted local simplification only: `bind_def`, `return_def`, `raise_def`, `check_def`, `lift_option_def`, `lift_option_type_def`, `get_accounts_def`, `get_transient_storage_def`, `update_accounts_def`, `update_transient_def`. Avoid broad `gvs` over the whole prefix.
- Keep C0.1.1.2.3 focused on reaching the concrete success continuation. Do not solve the optional-driver IH tail in this component if that belongs to C0.1.1.2.4; checkpoint when the single success path is exposed.
- Commit only reviewed stable progress with `git commit --no-gpg-sign`; current source has an uncommitted probe and must not be committed as-is.

### Oracle Feedback
- Held: E0047 evidence showed the branch-local wrapper plan was still too low-level; the strategist accepted and replaced it with the maintainer-approved linear proof path in TO_type_system_rewrite-20260601T081233Z_m1250_t001.
- Held: cleanup/audit components C0.1.1.2.0, C0.1.1.2.1, and C0.1.1.2.2 were reviewed and accepted; the source was build-clean before the probe edit.
- Missed/obsolete: previous guidance to prove static/nonstatic success-tail eliminators is now invalidated by E0047 and the replacement PLAN. Do not follow old STATE lines about C0.1.1.2.2.1.
- Current binding PLAN: C0.1.1.2.3 linear monadic branch proof first, then C0.1.1.2.4 local optional-driver IH application in the concrete success continuation.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1281_t003 - current PLAN/frontier: active C0.1.1.2.3, next work is linear ExtCall Resume proof
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1281_t002 - git status shows tracked source dirty plus untracked tmp/legacy files
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:17231 - `Expr_Call_ExtCall_result` currently contains temporary `FAIL_TAC` probe
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1250_t001 - strategist replaced wrapper-adapter path with linear branch proof plan
- episode:E0047 - static wrapper closed stuck/risk_mismatch; broad eliminator/witness-list approach ruled out
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1268_t001 - last clean holbuild before C0.1.1.2.3 probe edit
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1275_t002 - source around mutual proof suspend site showing ExtCall Resume entry point
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1276_t001 - source around `Expr_Call_ExtCall_result` and adjacent proof templates
