# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.5.4.2
- status: in_progress
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Prove `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_calldata_error]` at the new nonstatic ExtCall subresume block (around line 17971). Replace its `cheat` only; start with `RESUME_TAC`, rewrite concrete branch facts (`x <> []`, `TL x <> []`, `dest_AddressV (HD x) = SOME target_addr`, `dest_NumV (HD (TL x)) = SOME amount`, and `build_ext_calldata ... (TL (TL x)) = NONE`), then delete the large generated-prefix universal assumption before simplifying monadic definitions. Close via `extcall_nonstatic_runtime_error_sound`.
- expected_goal_shape: Active leaf C0.5.4.2. Source already has reviewed/committed C0.5.4.1 skeleton: parent `Expr_Call_ExtCall_result_nonstatic` derives target/amount/nonempty facts and suspends five branches; placeholder cheats remain for `Expr_Call_ExtCall_nonstatic_calldata_error`, empty-code, run-none, reverted, success. The calldata subresume goal should have concrete `build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL x)) = NONE` plus the suspended branch equation; if the large generated-prefix `!s'' vs t ...` antecedent is still present, remove it with `qpat_x_assum ... kall_tac` before any `simp[bind_def,raise_def]`.
- verify_with: holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=600)

## If This Fails
- If the calldata subresume still times out after the generated-prefix assumption is removed, call `checkpoint_progress` or `close_component(result='stuck', diagnosis_tag='risk_mismatch')` with the failing holbuild evidence; do not try broader `gvs`/`AllCaseEqs()` or generated-prefix adapter theorems. If it proves/builds, close C0.5.4.2 as proved, call mandatory `plan_oracle(mode='review')`, then commit only relevant tracked `semantics/prop` files with `git commit --no-gpg-sign`.

## Do Not Retry
- Reintroduce `extcall_nonstatic_projected_sound` or any helper with premise `eval_expr cx (Call ... ExtCall F ...) st = (res,st')`.: E0249 showed this full-call boundary recreates the generated-prefix timeout shape and is explicitly invalidated by the PLAN.
  - evidence: episode:E0249
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4670_t001
- Prove the nonstatic ExtCall Resume as one monolithic branch-by-branch proof with inline error closures.: E0253 showed the first calldata branch still times out on >4KiB generated-prefix goals; the repaired PLAN requires named subresumes.
  - evidence: episode:E0253
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4713_t001
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4715_t001
- Run `simp[bind_def, raise_def]`, broad `gvs`, or `AllCaseEqs()` in a nonstatic subresume while the large generated-prefix universal assumption is still in context.: Even targeted simplification timed out when that assumption remained. Delete the generated-prefix assumption first, then simplify only the concrete suspended equation.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4715_t001
  - evidence: plan:C0.5.4.2
- Stage/commit untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are pre-existing unrelated artifacts; commits should stage only relevant tracked task-owned files and use `--no-gpg-sign`.
  - evidence: tool_output:TO_type_system_rewrite-20260602T195240Z_m4733_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach now validated: the nonstatic ExtCall branch should be treated like the existing static branch, with parent skeleton + named `suspend` subresumes rather than one monolithic proof.
- Do not optimize `extcall_nonstatic_projected_state_well_typed` or resurrect `extcall_nonstatic_projected_sound`; those are the wrong abstraction for full mutual postcondition proof.
- The PLAN decomposition is now the right abstraction if each subresume can discard the generated-prefix universal before simplification. If a subresume still cannot, the branch boundary is still too late/early and should be escalated.
- Do not retry tactics on >4KiB generated-prefix timeouts. The next proof should be small: prove one calldata runtime-error branch using concrete branch facts and `extcall_nonstatic_runtime_error_sound`.
- A fresh expert should first inspect the suspended calldata goal and verify exactly which assumption is the large generated-prefix antecedent to delete before any monadic simplification.

### What Went Wrong
- The direct C0.5.4 branch-by-branch proof repeated the E0248/E0249 generated-prefix problem: even the first calldata error branch timed out on a >4KiB goal at `simp[no_type_error_result_def]` and then at targeted `simp[bind_def,raise_def]`.
- The failure was a proof-boundary issue, not a missing semantic fact: the branch facts were not top-level/concrete enough until the proof was decomposed with `suspend` subresumes.
- STATE on disk was stale from before this session; PLAN/DOSSIER/git history now carry the real status. This handoff cursor supersedes old STATE lines.

### Ignored Signals
- Earlier PLAN stop conditions explicitly said to stop on generated-prefix timeout; after one monolithic attempt failed, the correct move was strategist review, which produced the branch-suspended decomposition.
- The existing static ExtCall subresumes were the working pattern; the first nonstatic attempt underweighted that proof-shape evidence and tried to prove error branches inline.

### Strategy Adjustments
- Continue from active C0.5.4.2; do not call `begin_component` again unless the active component state has been cleared by the harness.
- For each nonstatic error subresume, first `RESUME_TAC`, rewrite concrete branch facts, then delete the large generated-prefix universal assumption before simplification. Use `extcall_nonstatic_runtime_error_sound` for the final postcondition.
- After C0.5.4.2, follow PLAN order: C0.5.4.3 for empty-code/run-none/revert, then C0.5.4.4 for success with `run_ext_call_accounts_well_typed` and `extcall_success_continuation_sound_cond_driver_ih`.
- Keep commits narrow and unsigned; untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` and `semantics/prop/tmp_helper.txt` remain unrelated and must not be staged.

### Oracle Feedback
- Held: E0253 review correctly diagnosed the monolithic nonstatic Resume as wrong-shaped and decomposed it into branch-suspended leaves.
- Held: C0.5.4.1 review accepted the skeleton with exactly five planned subresume placeholders; focused build passed, confirming the source shape is viable.
- Missed earlier: the first C0.5.4 plan still underestimated generated-prefix brittleness; subresume boundaries were needed from the start.

## Evidence Pointers
- episode:E0253 - monolithic C0.5.4 attempt closed stuck/risk_mismatch due generated-prefix timeout
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4713_t001 - timeout at first calldata error branch with >4KiB generated-prefix goal
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4715_t001 - targeted branch-local simplification still timed out while generated-prefix assumption remained
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4717_t001 - source reverted to stable cheated baseline before replanning
- episode:E0254 - C0.5.4.1 skeleton proved/reviewed
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4721_t001 - source edit adding parent skeleton and named nonstatic suspends
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4727_t001 - focused build passed with planned subresume placeholders
- tool_output:TO_type_system_rewrite-20260602T195240Z_m4733_t002 - query_plan shows active C0.5.4.2 and next calldata-error subresume guidance
