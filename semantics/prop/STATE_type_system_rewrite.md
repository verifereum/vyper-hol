# STATE_type_system_rewrite
Updated: 2026-05-14

## Cursor
- component: C3.1
- status: in_progress
- active_file: semantics/prop/vyperTypeStatePreservationScript.sml
- next_action: Build top_level_HashMapRef_assign_no_type_error to see goal at first cheat (compute_hashmap_slot). Fill in: derive hashmap_prefix ValueSubscript facts + compute_hashmap_slot_subscripts_to_values for compute_hashmap_slot <> NONE, Cases_on evaluate_type for evaluate_type <> NONE, then dispatch read/assign_subscripts/write/assign_result no-TypeError subgoals. Then rewrite sound_TopLevelVar resume to call the boundary lemma.
- expected_goal_shape: After split_hashmap_subscripts SOME case: goals at compute_hashmap_slot <> NONE and subsequent monadic steps. Each step has separate NONE/INR subgoals that contradict derived facts.
- verify_with: holbuild(targets=['vyperTypeStatePreservationTheory'])

## If This Fails
- If boundary lemma goal explosion >4KB: add intermediate helper lemmas for each monadic step. If compute_hashmap_slot alignment fails: check split_hashmap_subscripts_some_imp length agreement + hashmap_prefix_ValueSubscript.

## Do Not Retry
- gvs[bind_apply, AllCaseEqs(), lift_option_type_def, ...] to expand monadic do-block inside an assumption in the resume: gvs cannot expand bind chains inside assumptions. The do-block MUST be pushed to the goal first (mp_tac) or handled in a standalone lemma where the equation is the conclusion. 7+ episodes confirm this.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m2428_t001
  - evidence: episode:E0007
  - evidence: episode:E0012
- rw[well_formed_type_def] >> metis_tac[] to derive evaluate_type <> NONE from well_formed_type assumption: simp/metis cannot connect IS_SOME in assumption to <> NONE in goal. Use Cases_on evaluate_type result instead.
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m2393_t001

## Reflection
### Tunnel Vision Check
- After 6+ episodes failing on inline do-block expansion with gvs[bind_apply, AllCaseEqs(), ...], I finally switched to boundary lemma approach but didn't complete it before context ran out. The boundary lemma IS the right approach.
- The resume also has a parallel inline approach (lines 2240-2310) that derives all typing facts before expansion - this should be simplified to just call the boundary lemma once proved.
- I did not consider: can the entire resume sound_TopLevelVar branch be replaced by a call to top_level_HashMapRef_assign_no_type_error + existing Value branch code?

### What Went Wrong
- evaluate_type <> NONE fix (Cases_on) was known from STATE for multiple sessions but took most of this session to apply
- The gvs[bind_apply, AllCaseEqs()] approach for expanding the HashMapRef do-block has NEVER worked across 7+ episodes - gvs cannot expand bind chains inside assumptions
- I created the boundary lemma too late - should have done it immediately after the first gvs failure

### Ignored Signals
- STATE and prior episodes repeatedly recommended the boundary lemma fallback - I spent too long on inline approach
- The Cases_on pattern for IS_SOME <> NONE was solved in prior episodes but I kept trying simp/metis variants first
- LEARNING L0041 says: derive all typing facts BEFORE gvs expansion - works for facts but not for expansion itself

### Strategy Adjustments
- For the boundary lemma: use staged simp approach (Once assign_target_def then expand bind by bind)
- After the boundary lemma is proved, SIMPLIFY the resume: replace all inline HashMapRef proof code with a single drule call
- For ANY goal where gvs expansion of a monadic do-block in an assumption fails: immediately switch to boundary lemma

### Oracle Feedback
- PLAN C3.1 approach is correct: boundary lemma pattern works. Holdup was tactical (HOL4 monad expansion) not architectural
- The existing resume's parallel approach also works for fact derivation but the expansion step is still broken - boundary lemma solves this

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2420_t001 - evaluate_type <> NONE fix with Cases_on works
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2428_t001 - gvs FAIL probe: do-block remains unexpanded in assumption
- tool_output:TO_type_system_rewrite-20260513T211025Z_m2506_t001 - boundary lemma static error fixed by moving after helpers
