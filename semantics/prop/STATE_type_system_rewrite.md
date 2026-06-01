# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0
- status: unblocked_for_bounded_probe
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Replace the former external-precondition stop gate with a proof-only bounded probe for `eval_all_type_sound_mutual[Expr_Call_ExtCall]`. Edits are allowed only under `semantics/prop`; evaluator/semantics definitions must not change. Attempt a careful linear proof that steps through the ExtCall monadic chain one operation at a time, closes each error case immediately, and keeps one main success path active. Specialize the generated optional-driver IH only after reaching a single concrete ExtCall success-continuation branch with prefix operations already split/discharged.
- expected_goal_shape: Inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`, the proof should first close the `type_place_expr` half, unfold expression typing/evaluation once, split `eval_exprs` and subsequent ExtCall checks/lifts/run/update operations locally, and use IHs/helper lemmas immediately in focused branches. The driver IH should not be coerced into a compact standalone premise at the top-level Resume context.
- verify_with: During the probe, use focused `holbuild build vyperTypeStmtSoundnessTheory` for feedback. After ExtCall succeeds, continue with `Expr_Call_RawCallTarget`, `raw_call_return_type_well_formed`, then final `holbuild build vyperSemanticsHolTheory` with zero reachable fresh-stack CHEAT warnings.

## If This Fails
- If the bounded linear proof still requires broad generated-prefix simplification from the top-level Resume context, long qspecl_then over unsplit generated temporaries, ASSUME-quoted reconstruction, MATCH_MP/ACCEPT_TAC/CONJ plumbing over the full prefix, or an adapter theorem packaging the full prefix, stop and record exact holbuild evidence. Local specialization of the driver IH is allowed only after reaching a single concrete ExtCall success-continuation branch where the prefix operations have already been split/discharged.

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
- Proceed to Expr_Call_RawCallTarget, raw_call_return_type_well_formed, wrapper/final validation, or commits before the ExtCall bounded probe has either succeeded or been explicitly re-planned.: C0 remains required-for-completion and downstream work depends on resolving ExtCall first.
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0886_t001
  - evidence: tool_output:TO_type_system_rewrite-20260531T201607Z_m0897_t003
- Treat the new authorization as permission for arbitrary generated-prefix plumbing.: The only newly allowed generated-IH use is local specialization in a single concrete success-continuation branch after the prefix has been split/discharged.
  - evidence: user:2026-06-01 maintainer clarification

## Reflection
### Tunnel Vision Check
- The authorized route is proof-only: no evaluator/semantics changes, no edits outside `semantics/prop`.
- The useful outside-the-box idea is a disciplined proof decomposition, not a semantic refactor: follow the ExtCall monadic chain linearly, close error branches immediately, and use IHs when their branch premises become available.
- Likely wrong optimization target: improving extcall_success_continuation_sound_cond_driver_ih. It is useful only after the proof reaches the continuation point; the current probe should focus on reaching that point without exploding the generated prefix.
- Do not retry top-level generated-prefix tactics. E0029 remains evidence against broad simp/metis over the unsplit prefix, but maintainer clarification permits local driver-IH specialization after the prefix is split in one concrete success branch.

### What Went Wrong
- The replacement C0.1 assumption failed: moving the proof boundary locally inside the existing Expr_Call_ExtCall Resume did not expose a compact optional-driver premise.
- The first unfold/probe still showed the driver IH as a giant generated prefix implication over eval_exprs, checks/lifts, build_ext_calldata, run_ext_call, update_accounts, and update_transient.
- Continuing the approved split immediately ran into timeouts/failures on basic local simplification (gvs[no_type_error_result_def], simp[], and Cases_on is_static' >> gvs[]), so the Risk-2 rating was wrong, not merely a tactic choice.
- Experimental edits were reverted to the honest ExtCall cheat, and vyperTypeStmtSoundnessTheory builds at the cheated baseline.
- This session performed only startup/blockage assessment. query_plan still shows C0 Risk 4 BLOCKED with no frontier/beginable component, and git status shows only task memory/plan files plus a legacy LEARNINGS file modified/untracked.

### Ignored Signals
- Earlier evidence already warned that generated-prefix adapters were the wrong abstraction; C0.1 confirmed the same shape rather than derisking it.
- A local Resume boundary probe was authorized, but the first visible goal already exceeded 4KiB and contained the forbidden prefix shape; that should be treated as design failure, not a cue for more tactic search.
- The task says the proof should be entirely straightforward and to stop on design/plan issues; under the new clarification, the ExtCall bounded probe is authorized, but downstream RawCallTarget, builtin cleanup, commits, and final validation remain unauthorized until ExtCall is resolved or re-planned.
- Do not interpret query_plan's generic complete option as proof completion; task-owned cheats remain and C0 is required-for-completion.

### Strategy Adjustments
- Future sessions may start the bounded ExtCall proof probe directly in `semantics/prop/vyperTypeStmtSoundnessScript.sml`, using focused holbuild feedback.
- Future work should avoid recovering the optional driver IH from the unsplit generated full ExtCall prefix; instead reach the concrete success-continuation branch first, then specialize locally if needed.
- Keep runtime_consistent_get_tenv and extcall_success_continuation_sound_cond_driver_ih as potentially useful post-run continuation infrastructure, but do not build new helpers around the full generated driver IH.
- Commit discipline remains: all edits under semantics/prop only, and any future commit must use git commit --no-gpg-sign.

### Oracle / Maintainer Feedback
- Held from prior evidence: C0.1 failed as proof-interface evidence for top-level generated-prefix recovery, not as evidence that the ExtCall theorem is false.
- Held from prior evidence: generated-prefix adapters and broad generated-prefix simplification remain prohibited and wrong for this task's straightforward-proof contract.
- Updated by maintainer clarification: a bounded proof-only frontier now exists. It may step through the ExtCall monadic chain linearly and specialize the driver IH only after reaching a concrete success-continuation branch with prefix operations split/discharged.
- Missed by prior replacement: the local Resume-boundary probe was too coarse. The new probe must avoid exposing the whole prefix at once and must close branches as soon as they arise.

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
