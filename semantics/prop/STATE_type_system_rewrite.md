# STATE_type_system_rewrite
Updated: 2026-05-15

## Cursor
- component: C3.1
- status: in_progress
- active_file: semantics/prop/vyperTypeStatePreservationScript.sml
- next_action: Fix sound_TopLevelVar resume proof: replace assign_target_preserves_runtime_consistent_result (not yet defined at that point in file) with imp_res_tac (cj 1 assign_target_preserves_state_well_typed_mutual). Then build vyperTypeStatePreservationTheory to verify.
- expected_goal_shape: runtime_consistent env cx st' /\ no_type_error_result res after Cases_on vt splits into Type (StorageVarDecl/HashMapVarDecl) and HashMapT subcases
- verify_with: holbuild(targets=['vyperTypeStatePreservationTheory'], tactic_timeout=120)

## If This Fails
- If gvs[assign_target_assignable_context_def] doesn't destruct correctly after target_runtime_typed_def expansion, insert FAIL_TAC probe to see exact goal state. If metis_tac[branch_lemma] fails to match premises, check which specific premise is missing and add by-subgoal to derive it.

## Do Not Retry
- Using assign_target_preserves_runtime_consistent_result inside sound_TopLevelVar resume: This theorem is defined AFTER assign_target_sound_mutual in the same file (line ~3472) and depends on it - circular dependency. Use cj 1 assign_target_preserves_state_well_typed_mutual instead.
  - evidence: tool_output:TO_type_system_rewrite-20260515T192259Z_m10927_t001
- gvs[AllCaseEqs()] blast inline in Resume blocks for TopLevelVar: Creates 30+ subgoals with auto-generated variable names that prevent lemma matching. Use boundary lemma + metis_tac instead (L0335).
  - evidence: tool_output:TO_type_system_rewrite-20260513T211025Z_m6966_t002
- drule_all assign_target_HashMapRef_branch_no_type_error after gvs that substitutes first_sub/rest_subs: gvs substitutes first_sub->LAST sbs, rest_subs->TL(REVERSE sbs), making drule_all unable to match. Use metis_tac instead or apply drule before gvs (L0334).
  - evidence: tool_output:TO_type_system_rewrite-20260515T192259Z_m10877_t001

## Reflection
### Tunnel Vision Check
- The sound_TopLevelVar resume is the LAST cheat in vyperTypeStatePreservationScript.sml. Completing it finishes both C3.1 and C3.6 in one step. But I'm writing a complex inline proof in a Resume block - should I prove a standalone top_level_TopLevelVar_assign_no_type_error boundary lemma instead, like the pattern that worked for HashMapRef and ArrayRef?
- Is there a structural or ArrayTV/HashMapT type_value case I'm missing? The type_value nchotomy includes BaseTV, TupleTV, ArrayTV, StructTV, NoneTV - but for TopLevelVar, location_runtime_typed maps to FLOOKUP env.toplevel_vtypes which should only produce Type or HashMapT based on the well_typed_atarget typing. Need to verify this.
- The preservation part (runtime_consistent) should close easily from the already-proved preservation mutual theorem (cj 1). The no_type_error part needs the branch lemmas. This decomposition is correct.

### What Went Wrong
- Referenced assign_target_preserves_runtime_consistent_result which is defined LATER in the same file (line ~3472), causing a static error. This theorem depends on assign_target_sound_mutual itself - circular dependency. Must use the earlier preservation mutual theorem (assign_target_preserves_state_well_typed_mutual, finalized at line 1316) instead.

### Ignored Signals
- The DOSSIER episode E0052 confirms assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error builds successfully using imp_res_tac + metis_tac pattern. This same pattern should work in the resume.

### Strategy Adjustments
- For the resume, derive runtime_consistent first via imp_res_tac (cj 1 assign_target_preserves_state_well_typed_mutual) or similar, then prove no_type_error_result by splitting on vt type_value and calling the appropriate boundary lemma for each branch.
- Consider using a standalone boundary lemma (like top_level_TopLevelVar_assign_no_type_error) to keep the resume body minimal. This follows L0335 pattern.

### Oracle Feedback
- PLAN C3.1/C3.6 approach (boundary lemma then resume integration) is correct. The HashMapRef branch boundary lemma is proved. The ArrayRef branch boundary lemma is proved. The Type_StorageVarDecl boundary lemma is proved. All that remains is wiring them together in the resume.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10893_t001 - top_level_HashMapRef_assign_no_type_error builds clean after >- gvs[] + metis_tac fix
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10899_t001 - sound_TopLevelVar resume goal shape: runtime_consistent + no_type_error_result with target_runtime_typed + assign_target_assignable_context hypotheses
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10927_t001 - static error: assign_target_preserves_runtime_consistent_result not yet declared at resume point
