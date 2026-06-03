# STATE_callable_entry_initial_state
Updated: 2026-06-03

## Cursor
- component: C2
- status: blocked
- active_file: semantics/prop/vyperTypeInitialStateScript.sml
- next_action: Retry the required strategist review for closed proved episode E0005: plan_oracle(mode='review', component_id='C2', evidence_ids=['TO_callable_entry_initial_state-20260603T143413Z_m0047_t001','TO_callable_entry_initial_state-20260603T143413Z_m0063_t001'], planning_reason='review closed episode E0005'). If accepted, inspect git diff/status, optionally rerun holbuild(targets=['vyperTypeInitialStateTheory']), then commit the C2 proof. Do not begin C3 until this review succeeds.
- expected_goal_shape: No HOL goal expected immediately; PLAN gate shows Beginable now: none (pending strategist review). Source currently contains a proved C2 assembly proof and holbuild vyperTypeInitialStateTheory succeeded at tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0063_t001.
- verify_with: holbuild(targets=['vyperTypeInitialStateTheory'], timeout=600)

## If This Fails
- If plan_oracle review again fails only with OracleBudgetExceeded, do not edit/build; request handoff/blocked per harness guidance. If holbuild fails, read the failing goal, checkpoint_progress for C2 if the source proof regressed, and do not start C3.

## Do Not Retry
- Begin C3 or edit/build corollaries before C2 strategist review is accepted.: PLAN gate says beginable now none pending C2 review; proceeding would violate the structured PLAN gate.
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0069_t003
- Retry C2 proof by unfolding functions_well_typed_def in the main theorem.: C2 already builds using the C1.4 boundary lemma; unfolding would abandon the planned abstraction and duplicate helper work.
  - evidence: episode:E0005
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0063_t001
- Use qexistsl [`env_body`,`env_after`,`initial_state am [scope]`] in the C2 proof after simplifying the existential.: After the st equality is simplified, only env_body/env_after remain existential; the extra witness caused 'goal not an exists'.
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0050_t001
- Instantiate bind_arguments_env_scopes_consistent by guessing qspecl_then with an initial_state term witness.: The polymorphic/record witness parse failed; the successful pattern was to state a sufficiency goal with `(initial_state am [scope]) with scopes := [scope]`, use irule, then provide existential witnesses in order args, get_tenv cx, vals.
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0053_t001
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0055_t001
  - evidence: tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0063_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box approach not tried: use the existing vyperTypeCallSoundness.functions_well_typed_body wrapper for C1.4 instead of unfolding functions_well_typed_def directly. Direct unfolding worked, but wrapper could reduce future maintenance.
- The PLAN decomposition still looks right: C1 boundary lemmas made C2 a short assembly proof; no definition change or new helper appears needed for C2.
- Fresh expert would first question whether pending strategist review is merely procedural. It is: DOSSIER has E0005 proved and holbuild success, but PLAN gate blocks C3 until review is accepted.
- Do not optimize the C2 proof further before review unless the oracle rejects it; remaining work is procedural review then corollaries.

### What Went Wrong
- The required plan_oracle review for C2 failed twice with OracleBudgetExceeded after close_component recorded E0005. This left PLAN gate pending review even though source and holbuild show C2 proved.
- Several routine tactic failures came from theorem-instantiation shape, not theorem falsehood: qexistsl supplied a witness for st after simplification had already consumed the st equality; qspecl_then failed parsing the polymorphic initial_state witness; irule on bind_arguments_env_scopes_consistent needed explicit existential witnesses after matching.

### Ignored Signals
- After C2 close, query_plan explicitly showed 'Beginable now: none (pending strategist review)'; obey this and do not proceed to C3 in the next session until review succeeds.
- The state file did not exist yet; save_handoff is now creating the executor cursor rather than relying on a pre-existing STATE file.

### Strategy Adjustments
- For plan_oracle review after a closed episode, keep the request minimal (no reads unless asked) to avoid context/budget pressure; the evidence IDs and DOSSIER episode are enough.
- When applying exported lemmas with existential variables after irule, inspect the generated existential order from holbuild before qexistsl; do not guess witness order.
- Preserve the boundary-lemma abstraction in C3/C4; avoid unfolding functions_well_typed_def in C3.

### Oracle Feedback
- Strategist insight held: instantiate functions_well_typed with fn_sigs and FEMPTY static maps; C1.4 and C2 both built using this route.
- Strategist insight held: de-localizing bind_arguments_env_scopes_consistent and bind_arguments_scope_well_typed_stmt avoided duplicate helper proofs.
- Missed reality only procedurally: oracle review could not complete due to OracleBudgetExceeded, not due to a proof/design issue.

## Evidence Pointers
- episode:E0005 - C2 closed as proved; source kept; main theorem cheat replaced by assembly proof.
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0063_t001 - holbuild vyperTypeInitialStateTheory succeeded after the C2 proof edits.
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0065_t001 - first C2 strategist review attempt failed with OracleBudgetExceeded.
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0067_t001 - second minimal C2 strategist review attempt also failed with OracleBudgetExceeded.
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0069_t003 - current PLAN gate: C2 done but pending strategist review; beginable now none; allowed next action is C2 review.
- tool_output:TO_callable_entry_initial_state-20260603T143413Z_m0069_t002 - STATE file was absent before handoff.
