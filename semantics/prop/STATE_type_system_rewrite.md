# STATE_type_system_rewrite
Updated: 2026-05-14

## Cursor
- component: C3.2
- status: in_progress
- active_file: semantics/prop/vyperTypeStatePreservationScript.sml
- next_action: Rewrite assign_target_ArrayRef_Replace_ntr_v2 (line 2723) and assign_target_ArrayRef_Update_ntr_v2 (line 2775) using the PROVEN AppendOp_ordinary_ntr pattern (lines 2827-3031): Cases_on final_tv BEFORE expanding assign_target_def, then per-constructor mp_tac+simp+gvs[AllCaseEqs()] producing 4 subgoals each. Rename to _v3 to break stale holbuild checkpoint. Update caller assign_target_TopLevelVar_ArrayRef_branch_no_type_error (line 3089) to use _v3 names.
- expected_goal_shape: Per constructor (BaseTV, TupleTV, StructTV, FlagTV, NoneTV, ArrayTV Fixed/Dynamic): 4 subgoals after gvs[AllCaseEqs()] - success (assign_result), write INR, assign INR, read INR. ArrayTV Dynamic case contradicts Replace/Update (no Dynamic exclusion needed). Dispatch with drule chains for value_has_type + lemma application.
- verify_with: holbuild(targets=['vyperTypeStatePreservationTheory'])

## If This Fails
- If Cases_on approach also fails from stale checkpoint: insert dummy [local] theorem BEFORE both _v3 lemmas to force fresh theory-context checkpoint. If gvs[AllCaseEqs()] still explodes per constructor: fall back to step-by-step Cases_on monadic results (read_storage_slot etc.) after Cases_on final_tv + mp_tac + simp WITHOUT AllCaseEqs.

## Do Not Retry
- gvs blast pattern with by-subgoals referencing final_tv UNDER stale holbuild checkpoint: Stale checkpoint replays old variable bindings where final_tv was substituted differently by AllCaseEqs. The by-subgoal creates a FRESH final_tv that triggers DISCH_THEN assertion failure at proof_runtime.sml:749. Must break stale checkpoint first (rename theorem + all_tac >> prefix or dummy [local] theorem insertion).
  - evidence: tool_output:TO_type_system_rewrite-20260514T195458Z_m8323_t001
  - evidence: tool_output:TO_type_system_rewrite-20260514T195458Z_m8062_t003
- Cases_on intermediate monadic result variables (q, x) after partial gvs expansion: Variable names from Cases_on depend on checkpoint replay bindings. Stale checkpoints give wrong names. Also, intermediate results are nested inside case expressions that Cases_on cannot reach directly.
  - evidence: tool_output:TO_type_system_rewrite-20260514T195458Z_m8309_t001
  - evidence: tool_output:TO_type_system_rewrite-20260514T195458Z_m8171_t001

## Reflection
### Tunnel Vision Check
- The AppendOp_ordinary_ntr proof (lines 2827-3031) is ALREADY PROVEN with the exact Cases_on final_tv approach that I need. I spent zero time actually implementing this fix - should have immediately rewritten Replace/Update on turn 1 instead of re-reading code.
- Consider merging all 4 ordinary branch lemmas (Replace, Update, AppendOp_ordinary, PopOp_ordinary) into a SINGLE parameterized lemma taking arbitrary op. The AppendOp proof is ~200 lines of near-identical per-constructor boilerplate. A single lemma would eliminate ~600 lines of duplication and make future fixes a single-point change.
- The gvs blast approach (PopOp_ordinary_ntr pattern) technically works too - the only blocker is stale holbuild checkpoints. If renaming to _v3 doesn't break the checkpoint, try the compact 40-line gvs blast version FIRST since it's much shorter.

### What Went Wrong
- This entire session was wasted re-reading context that STATE already summarized. STATE explicitly said 'Rewrite using PopOp_ordinary_ntr gvs blast pattern' from E0075. I should have edited and built immediately.
- The stale checkpoint issue is the real blocker, not the proof approach. The Replace/Update proofs ARE structurally identical to PopOp_ordinary_ntr. If I had renamed the theorems to _v3 FIRST then built, the gvs blast would likely work.
- Did not attempt any edits this session - just read and built. The fix is straightforward: rename, maybe add all_tac >> prefix, and the PopOp pattern should work.

### Ignored Signals
- STATE said 'Build vyperTypeStatePreservationTheory to test the rewritten Replace_ntr_v2 and Update_ntr_v2 proofs' as the very first action. I did this but didn't follow up with edits.
- E0075 already identified assign_operation_CASE_rator as the key difference between failing and working proofs. The PopOp_ordinary_ntr proof has it and works. Replace/Update v2 now also have it. The remaining issue is purely the stale checkpoint.
- Previous sessions added many [local] dummy theorems to break checkpoints (L0174, L0177). Should have inserted one before Replace_ntr_v2 to break the stale checkpoint.

### Strategy Adjustments
- IMMEDIATELY rename and rewrite failing proofs on first action next session. Stop re-reading proven working code.
- Try the compact gvs blast (PopOp pattern, ~40 lines) FIRST with fresh theorem names (_v3) + all_tac >> prefix to break checkpoint. Only fall back to verbose Cases_on approach if blast fails.
- Insert dummy [local] theorems aggressively when holbuild reports stale checkpoint matching.

### Oracle Feedback
- Oracle decomposition (split by operation, ordinary for rest) is correct. The proofs DO work - PopOp_ordinary_ntr proves it.
- Oracle suggestion to merge 4 lemmas into one parameterized lemma is still the right cleanup after individual proofs work.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260514T195458Z_m8323_t001 - Replace_ntr_v2 build failure: stale checkpoint + by-subgoal DISCH_THEN assertion on final_tv after AllCaseEqs expansion
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3033-3087 - PROVEN PopOp_ordinary_ntr with gvs blast pattern
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2827-3031 - PROVEN AppendOp_ordinary_ntr with Cases_on final_tv pattern
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2723-2773 - FAILING Replace_ntr_v2
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2775-2825 - FAILING Update_ntr_v2
