# STATE_type_system_rewrite
Updated: 2026-05-18

## Cursor
- component: C4.1.1
- status: in_progress
- active_file: semantics/prop/vyperTypeBuiltinsScript.sml
- next_action: Fix remaining 3 items in vyperTypeBuiltinsScript.sml: (1) Replace concat_string_builtin_no_type_error proof body to use direct proof like concat_bytes_no_type_error (drule LIST_REL_value_has_type_imp_combined then unfold). (2) Replace slice_builtin_no_type_error with two separate helpers: slice_bytes_no_type_error (ty = BaseT(BytesT(Dynamic n)), HD ts = BaseT(BytesT bd)) and slice_string_builtin_no_type_error (ty = BaseT(StringT n), HD ts = BaseT(StringT m)), each with direct proof following slice_no_type_error pattern. (3) Update main dispatcher well_typed_builtin_app_no_type_error: change 'irule concat_builtin_no_type_error' to 'TRY (irule concat_bytes_no_type_error >> gvs[] >> NO_TAC) >> TRY (irule concat_string_builtin_no_type_error >> gvs[] >> NO_TAC)' and 'irule slice_builtin_no_type_error' to 'TRY (irule slice_bytes_no_type_error >> gvs[] >> NO_TAC) >> TRY (irule slice_string_builtin_no_type_error >> gvs[] >> NO_TAC)'. Then holbuild vyperTypeBuiltinsTheory.
- expected_goal_shape: After gvs[well_typed_builtin_app_def] in main dispatcher, Concat/Slice each produce separate bytes/string subgoals. New helpers match each subgoal directly via irule. Build should progress past the Concat/Slice helpers and the main dispatcher.
- verify_with: holbuild(targets=['vyperTypeBuiltinsTheory'], tactic_timeout=120, timeout=600)

## If This Fails
- If a helper proof fails, insert FAIL_TAC probe to see goal state. If dispatcher irule doesn't match after gvs, check whether gvs changes the conclusion shape (evaluate_builtin -> evaluate_concat). If structural issue across >3 helpers, escalate to plan_oracle.

## Do Not Retry
- Disjunctive helper lemma premises (∨) for Concat/Slice: gvs splits disjunctions, irule can't match: gvs[well_typed_builtin_app_def] splits disjunctions into separate subgoals. Helpers with ∨ premises never match non-disjunctive post-gvs goals.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m25561_t001
- qpat_x_assum `_ ∨ _` DISJ_CASES_TAC in helper proofs: qpat_x_assum cannot match generic disjunction pattern. After gvs resolves ty, the ∨ is already eliminated.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m25561_t001
- rpt strip_tac on !msg. f ≠ INR(TypeError msg) goals: Strips the ≠ into F with negated equation in assumptions, preventing simp from rewriting evaluate_builtin_def. Use strip_tac >> gen_tac instead.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m25409_t001
- irule concat_no_type_error/concat_string_no_type_error after gvs[] in Concat helper wrappers: concat_no_type_error needs type_slot_size and n < dimword(:256) premises that irule can't derive from the post-gvs goal state. Must prove directly using LIST_REL_value_has_type_imp_combined + evaluate_builtin_def expansion.
  - evidence: tool_output:TO_type_system_rewrite-20260516T153850Z_m25602_t002

## Reflection
### Tunnel Vision Check
- The core problem across sessions is the same: gvs[well_typed_builtin_app_def] splits disjunctions into separate subgoals, so helper lemmas MUST NOT have disjunctive premises. This applies to any future helper lemma too - check for ∨ in premises before writing one.
- I've been fixing helpers one at a time across multiple sessions. The next session should batch-fix ALL remaining issues (concat_string, slice split, dispatcher update) in one edit cycle, then build ONCE.
- The irule-before-expansion pattern is correct for most helpers but WRONG for Concat/Slice where the helper does the full proof itself (not delegating to an eval-helper via irule). For Concat/Slice, the new helpers use direct proofs that expand evaluate_builtin_def themselves.

### What Went Wrong
- concat_bytes_no_type_error proof attempted irule concat_no_type_error after gvs[] but this couldn't derive the required type_slot_size and n < dimword bounds from the assumptions. The fix: prove directly following the concat_no_type_error pattern (drule LIST_REL_value_has_type_imp_combined then unfold evaluate_builtin_def).
- concat_string_builtin_no_type_error still has the old broken irule-based proof that will fail for the same reason.
- slice_builtin_no_type_error still has disjunctive premises and uses rpt strip_tac + qpat_x_assum DISJ_CASES_TAC which are both known-broken patterns.
- Main dispatcher references non-existent concat_builtin_no_type_error - was never updated to use the two split helpers.

### Ignored Signals
- LEARNING L0931 explicitly documented the need for non-disjunctive helper premises. I should have applied this immediately to ALL helpers (concat_string + slice) rather than fixing only concat_bytes.
- LEARNING L0927 documents strip_tac >> gen_tac for ∀msg goals. The slice helper still uses rpt strip_tac which will break the proof.
- The concat_string helper will likely fail for the same reason concat_bytes did (irule after gvs can't derive type_slot_size bounds). I should have fixed it proactively in the same edit.

### Strategy Adjustments
- Batch-fix ALL remaining helper proof issues in a single edit cycle before building: concat_string direct proof, slice bytes/string split, dispatcher irule updates.
- Always verify that main dispatcher irule references match actual helper theorem names before building.
- For Concat/Slice helpers, NEVER use irule to underlying eval-helpers after gvs[]. Instead prove directly by reproducing the eval-helper's proof pattern.

### Oracle Feedback
- PLAN C4.1.1.2 was exactly right: 'Each helper should name one concrete builtin constructor and internally choose bytes vs string branch'. The current source still has the disjunctive slice helper violating this.
- PLAN correctly identified irule-before-expansion as the key pattern. This works for keccak256/sha256/as_wei_value where the eval-helper doesn't need type_slot_size bounds. But for Concat/Slice, the eval-helpers need evaluate_type-derived bounds that aren't available via simple irule delegation.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260516T153850Z_m25602_t002 - current build failure at concat_bytes_no_type_error
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1916-1953 - current state of concat_bytes (fixed) and concat_string (still broken)
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1955-1973 - current slice helper (still has disjunction premises)
- source:semantics/prop/vyperTypeBuiltinsScript.sml:2010-2013 - dispatcher still references non-existent concat_builtin_no_type_error
