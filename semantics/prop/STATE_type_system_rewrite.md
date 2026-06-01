# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.3.4
- status: blocked
- active_file: semantics/prop/vyperTypeStmtSoundnessScript.sml
- next_action: Retry the mandatory strategist review for closed proved episode E0089: plan_oracle(mode='review', component_id='C0.3.4', evidence_ids=['TO_type_system_rewrite-20260601T081233Z_m1907_t001','TO_type_system_rewrite-20260601T081233Z_m1908_t001'], planning_reason='review closed episode E0089'). Do not edit/build/begin C0.3.3 until this review gate is accepted.
- expected_goal_shape: No HOL goal should be entered while blocked. C0.3.4 source already contains the new local helpers `eval_extcall_args_error_any_call_ty` and five `*_any_call_ty_*` projections; `vyperTypeStmtSoundnessTheory` built successfully. Current blocker is only the pending strategist review, with two OracleBudgetExceeded failures.
- verify_with: After C0.3.4 review is accepted, optionally re-run holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300) before committing; then commit task-local stable changes with git commit --no-gpg-sign.

## If This Fails
- If plan_oracle review again returns OracleBudgetExceeded and query_plan still says review is the only allowed action, do not begin C0.3.3 or build. Either retry review if allowed by the harness or use end_session(outcome='blocked' or handoff as directed) with evidence TO_type_system_rewrite-20260601T081233Z_m1910_t001/TO_type_system_rewrite-20260601T081233Z_m1912_t001/TO_type_system_rewrite-20260601T081233Z_m1911_t001.

## Do Not Retry
- Begin or edit C0.3.3 before C0.3.4 review acceptance.: query_plan reports Beginable now: none and allowed next action is only the C0.3.4 strategist review; proceeding would violate the structured gate even though C0.3.3 is Oracle next after review.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1911_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1914_t004
- Retry C0.3.3 using old narrow C0.3.2 helpers (`eval_extcall_args_error_*`) over `Call ret_type (ExtCall ... ret_type)`.: E0084 showed the live Resume call has independent outer annotation `Call v15 ...`; old helpers fail to match. Use new `*_any_call_ty*` helpers after review instead.
  - evidence: episode:E0084
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1867_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1907_t001
- Force the helper mismatch in raw Resume with broad `simp`/`gvs`/`AllCaseEqs()` or generated-prefix adapter theorems.: Maintainer clarification and prior episodes forbid broad generated-prefix cleanup; previous attempts timed out under the >4KiB optional-driver prefix. The accepted repair is outside-Resume boundary/projection helpers.
  - evidence: episode:E0081
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1811_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1818_t001
- Use `reverse conj_tac` at the start of `Expr_Call_ExtCall_result` Resume.: Prior build evidence showed the first subgoal is the expression-result postcondition; reversing puts the place-expression tactic on the wrong goal.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1863_t001
  - evidence: episode:E0084

## Reflection
### Tunnel Vision Check
- Outside-the-box option not yet needed: instead of only projections, a generalized full-postcondition helper over `Call call_ty (ExtCall ... ret_type)` could be added and projections derived from it; current C0.3.4 projections already build, so consider this only if C0.3.3 still needs a broader boundary.
- Do not optimize the ExtCall success branch yet. The next proof component after review is C0.3.3: argument-error/place shell using the new generalized projections, not C0.4/C0.5 success-prefix work.
- The PLAN decomposition still looks right: small outside-Resume boundary lemmas first, then a Resume consumer, then linear success-path branches. The only current problem is an oracle review budget gate, not theorem design.
- If C0.3.3 does not accept the `*_any_call_ty_*` projections by direct `irule`, question the helper statement/goal shape first rather than trying broad simplification in the generated Resume context.
- A fresh expert should first verify the mandatory review gate is accepted, then inspect the diff and commit C0.3.4 before touching the Resume.

### What Went Wrong
- The earlier scheduler/frontier inconsistency was repaired by replacing/carrying forward the PLAN, and C0.3.4 became beginable. That resolved the prior STATE blocker.
- C0.3.4 proof itself was straightforward and build-clean, but the required strategist review after closing E0089 failed twice with OracleBudgetExceeded, leaving query_plan in a pending-review state with no beginable component.
- A holbuild attempt after C0.3.2 was rejected because no component was active; this was harmless but reinforced that build/commit discipline must respect the active/review gate.

### Ignored Signals
- After C0.3.4 was proved, query_plan explicitly said the only allowed next action was the C0.3.4 review. Do not treat C0.3.3 being listed as Oracle next as permission; Beginable now is none until review acceptance.
- The old STATE still mentioned the pre-C0.3.4 scheduler block. It is now stale: C0.3.4 has been edited and built successfully; the live blocker is strategist review budget, not scheduler ordering.

### Strategy Adjustments
- Next session should begin with git status and query_plan, then immediately retry the required plan_oracle review for E0089 using evidence IDs, without editing/building first.
- If review is accepted, inspect git diff under semantics/prop and commit the stable C0.3.4 checkpoint unsigned. Include tracked PLAN/DOSSIER/STATE/LEARNINGS changes if they are task-owned; leave `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` and `semantics/prop/tmp_helper.txt` untracked unless explicitly instructed.
- Only after accepted review/commit should C0.3.3 begin. Use `conj_tac`, not `reverse conj_tac`; use generalized `*_any_call_ty_*` helpers in the `INR` branch; keep broad raw Resume simplification forbidden.

### Oracle Feedback
- Held: E0084 diagnosis was correct. Generalizing the outer `Call` annotation to `call_ty` fixed the helper-interface problem outside the Resume context, and the target built.
- Held: The old narrow C0.3.2 helpers remain valid but not directly consumable in the live `Call v15 ...` Resume goal.
- Missed/blocked operationally: mandatory review could not complete because plan_oracle returned OracleBudgetExceeded twice after E0089, even though proof/build evidence is clean.
- Held: Maintainer constraints were respected: no evaluator/semantics edits, no files outside semantics/prop, no raw generated-prefix simplification, and no optional-driver IH specialization.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1907_t001 - edit inserted `eval_extcall_args_error_any_call_ty` and five generalized projections in vyperTypeStmtSoundnessScript.sml
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1908_t001 - holbuild of vyperTypeStmtSoundnessTheory succeeded after C0.3.4 helper additions
- episode:E0089 - C0.3.4 closed proved with source kept; dossier records helper family and build success
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1910_t001 - first mandatory C0.3.4 review attempt failed with OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1912_t001 - second mandatory C0.3.4 review attempt failed with OracleBudgetExceeded
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1911_t001 - query_plan shows C0.3.4 done but no component beginable pending strategist review
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1914_t004 - handoff query_plan confirms same pending-review gate
