# STATE_type_system_rewrite
Updated: 2026-06-02

## Cursor
- component: C0.2.1
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Run git status --short and query_plan(). If query_plan still reports blocking episode C0.2.1@E0158 and no frontier, call plan_oracle(mode='review', component_id='C0.2.1', evidence_ids=['TO_type_system_rewrite-20260601T220715Z_m3236_t001','TO_type_system_rewrite-20260601T220715Z_m3232_t001','TO_type_system_rewrite-20260601T220715Z_m3225_t001','TO_type_system_rewrite-20260601T220715Z_m3227_t001'], planning_reason='review closed episode E0158'). If that still returns OracleBudgetExceeded, call end_session(outcome='blocked', blocked_kind='external_precondition') rather than editing/building or handing off again.
- expected_goal_shape: No HOL proof goal is currently authorized. query_plan shows high-risk C0/C0.2/C0.2.1, no scheduled leaf frontier, beginable now none, blocking episode C0.2.1@E0158, and only the required strategist review action. Source is build-clean on the localized placeholder baseline: `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static_success]: cheat QED`.
- verify_with: Before unblocked: git status --short; query_plan() only. Do not run holbuild while pending strategist review blocks scheduling. After a successful review/replacement creates a beginable low-risk leaf, begin that component and verify relevant proof edits with holbuild(targets=['vyperTypeStmtSoundnessTheory'], timeout=300).

## If This Fails
- If plan_oracle review succeeds, follow the returned PLAN exactly; if it reauthorizes C0.2.1 without a genuinely new boundary, close/escalate rather than retrying ruled-out prefix splitting. If plan_oracle returns OracleBudgetExceeded or query_plan still has no frontier, report blocked with evidence TO_type_system_rewrite-20260601T220715Z_m3242_t001 and TO_type_system_rewrite-20260601T220715Z_m3243_t001.

## Do Not Retry
- Retry C0.2.1 as `RESUME_TAC` followed by linear splitting through `build_ext_calldata`, account lookup, `run_ext_call`, `check success`, and updates in the current resumed goal.: Prior C0.2.1 E0108 and current E0157/E0158 evidence show this exact shape remains >4KiB and non-straightforward before reaching the intended tail; repeating it violates task stop conditions.
  - evidence: episode:E0108
  - evidence: episode:E0158
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3225_t001
- Use broad `simp`/`gvs`, `AllCaseEqs()`, `drule_all`, `metis_tac`, or a long generated-prefix adapter theorem to recover the optional-driver IH/premise from the generated ExtCall prefix.: This is explicitly forbidden by the task/PLAN and repeatedly timed out or required brittle prefix plumbing; it treats a boundary mismatch as tactic search.
  - evidence: episode:E0149
  - evidence: episode:E0157
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3166_t001
- Call plan_oracle(mode='augment') or begin downstream work while E0158 is awaiting required review.: The harness blocks scheduling on the unresolved stuck episode; query_plan allows only plan_oracle(mode='review') for C0.2.1@E0158 until the review resolves.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3241_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3245_t003
- Begin C0.3/nonstatic ExtCall, RawCallTarget, or final audit while static ExtCall success remains cheated/localized and C0.2.1@E0158 is unresolved.: Static ExtCall is required for completion and the scheduler currently has no beginable frontier. Downstream work cannot make the task complete while the required static success Resume remains a placeholder.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3234_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3245_t003
- Stage or commit `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` or `semantics/prop/tmp_helper.txt`.: They are known pre-existing untracked artifacts outside stable task progress. Commits should stage only relevant tracked files under semantics/prop and use --no-gpg-sign.
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3222_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T220715Z_m3218_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach still unresolved: change the proof boundary so the static ExtCall optional-driver premise is produced by a helper/suspension before or exactly at a small tail obligation, not by replaying the generated ExtCall prefix inside the suspended mutual proof.
- We are likely optimizing the wrong proof boundary, not the wrong tactic. C0.1 localized the cheat, but C0.2/E0157 showed the localized Resume still contains generated-prefix projection obligations rather than a small tail-helper goal.
- The current PLAN decomposition is not executable until E0158 is reviewed. The active leaf C0.2.1 was closed stuck specifically because its plan repeated a same-shape prefix-splitting proof already contradicted by prior scoped evidence.
- Do not retry tactics when the needed change is a new helper/boundary lemma or a strategist/operator decision that this is blocked under the task's stop-if-not-straightforward instruction.
- A fresh expert should first question why `suspend` at `Expr_Call_ExtCall_result_static_success` still resumes to projection goals containing the whole generated prefix, and whether the mutual proof/suspension mechanism needs a different cut point or helper theorem.

### What Went Wrong
- C0.1 succeeded and was committed: static ExtCall was refactored so the old direct static Resume now suspends `Expr_Call_ExtCall_result_static_success`, with the remaining cheat localized there. Strategist accepted E0156; commit 1732439ce records the stable checkpoint.
- C0.2 failed: raw FAIL and `RESUME_TAC` probes showed the new branch-local Resume still has >4KiB generated-prefix projection goals. It was not a direct `extcall_success_continuation_*` tail-helper application as the plan assumed.
- The strategist replacement after E0157 initially rescheduled C0.2.1 as the same linear prefix-through-ExtCall proof. The scoped dossier already contained prior same-shape E0108 failures, so C0.2.1 was closed stuck without retrying.
- Required strategist review of E0158 could not complete: repeated plan_oracle(mode='review') calls returned OracleBudgetExceeded, leaving query_plan with high-risk blockers and no frontier.

### Ignored Signals
- The C0.2.1 scoped dossier itself warned that the linear static Resume prefix proof was already tried and found non-straightforward; this should dominate any new plan text that merely repeats that approach.
- A goal state >4KiB is a proof-interface signal here. The current C0.2 proof shape still exposes the generated optional-driver prefix and should not be simplified globally.
- Scheduler output matters: after E0158, query_plan explicitly says only the pending strategist review is allowed. Do not switch to C0.3 or RawCallTarget even if they appear ready in stale/queued plan text.
- A successful holbuild after restoring `cheat` validates only a stable placeholder baseline, not proof completion.

### Strategy Adjustments
- Next session should treat the first action as operational unblocking: obtain successful plan_oracle review for E0158, or report blocked if oracle budget is still exceeded. Do not do proof/source edits before that review.
- If a new plan is returned, require a genuinely new proof boundary/helper shape. It should not merely restate `RESUME_TAC` plus linear splitting through the same generated prefix.
- If unblocked, begin exactly the scheduled low-risk component, inspect scoped DOSSIER before edits, and stop immediately if the proposed proof again has the E0108/E0157 >4KiB generated-prefix shape.
- Keep commit hygiene: use git commit --no-gpg-sign; stage only tracked relevant files under semantics/prop; never stage semantics/prop/LEARNINGS_type_system_rewrite.legacy.md or semantics/prop/tmp_helper.txt.

### Oracle Feedback
- Held: C0.1 branch-local suspension refactor was valid and accepted; it created the C0.2 target but did not prove static ExtCall success.
- Missed: The first C0.2 replacement assumed that the suspended goal was already a small tail-helper application; E0157 showed it remained pre-tail and >4KiB.
- Missed again: The later C0.2.1 replacement reauthorized a linear prefix proof despite scoped prior E0108 and current E0157 evidence that this exact shape is non-straightforward under the task constraints.
- Current operational reality: plan_oracle review is required but blocked by OracleBudgetExceeded; this is now an external precondition for further sound proof work.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3217_t001 - strategist accepted C0.1/E0156 branch-local suspension refactor
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3221_t001 - unsigned commit 1732439ce saved the stable C0.1 checkpoint
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3225_t001 - raw C0.2 static-success Resume goal exceeded 4KiB and still contained generated prefix
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3227_t001 - `RESUME_TAC` split but first goal remained large generated-prefix `state_well_typed st'` projection
- episode:E0157 - C0.2 closed stuck/risk_mismatch and restored source to build-clean localized placeholder
- episode:E0158 - C0.2.1 closed stuck because its plan repeated the ruled-out linear prefix proof
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3242_t001 - required E0158 review still returned OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3245_t003 - latest query_plan: no frontier, pending strategist review C0.2.1@E0158 only
- tool_output:TO_type_system_rewrite-20260601T220715Z_m3230_t001 - build-clean localized placeholder baseline before E0158 closure
