# LEARNINGS_type_system_rewrite

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0309 scope='C3' tags=ArrayRef,pair_case,Cases_on
shape: Assign_target ArrayRef pair-case (ao, final_tv) proof pattern
pattern: Cases_on op BEFORE expanding assign_target_def. Per operation: derive resolve_array_element facts, expand inside operation-specific boundary lemma. Replace/Update: gvs blast + metis_tac[4 generic array_ref_ordinary_branch_* helpers]. AppendOp/PopOp Dynamic: separate boundary lemmas with get_storage_backend Cases_on BEFORE expansion. Ordinary AppendOp/PopOp: add Dynamic exclusion premise.
works_when: Proving no_type_error_result for assign_target TopLevelVar ArrayRef branch
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2703-2721
- source:semantics/vyperStateScript.sml:906-938

## L0311 scope='C3' tags=measureInduct,assignment_value
shape: Proving properties over assignment_value with nested list recursion (TupleTargetV)
pattern: Use measureInduct_on assignment_value_size gv. Add local lemma: MEM tgt l ==> assignment_value_size tgt < list_size assignment_value_size l + 1. Induct_on gv gives case analysis only.
works_when: Proving properties of assignment_value where P needs to hold for TupleTargetV list sub-elements
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1024-1054

## L0314 scope='global' tags=API,conjunction,corruption
shape: HOL4 conjunction //\ corrupted by API in term quotations
pattern: API corrupts //\ to non-ASCII. Use nested implication (==>) instead of conjunction, or split into separate theorems.
works_when: Writing Theorem statements with conjunction via tool API
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2703-2721

## L0315 scope='global' tags=env.type_defs,drule,bridging
shape: env.type_defs vs get_tenv cx mismatch blocking drule/irule
pattern: When fs[] rewrites env.type_defs->get_tenv cx, lemmas using env.type_defs won't match. Fix: derive env.type_defs form via metis_tac before fs[], OR use get_tenv cx form after fs[], OR single fs[all_needed_lemmas] may chain before elimination.
works_when: Applying typing lemmas after fs/gvs rewrites env.type_defs to get_tenv cx
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:631-660

## L0316 scope='global' tags=metis_tac,boundary_lemma
shape: metis_tac vs drule/irule for boundary lemmas with many variables
pattern: For boundary lemmas with 5+ antecedents matching assumptions: use metis_tac[boundary_lemma]. metis handles assumption matching and existential resolution automatically.
works_when: Goal is no_type_error_result and boundary lemma has right conclusion with many antecedents
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2407-2451

## L0317 scope='global' tags=lookup_global,contradiction
shape: lookup_global result shape constrains var_decl_info constructor
pattern: Contradiction lemmas: lookup_global_Value_not_HashMapVarDecl, lookup_global_ArrayRef_not_StorageVarDecl, lookup_global_HashMapRef_not_StorageVarDecl. Proof: mp_tac equation >> simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs(), var_decl_info_CASE_rator, prod_CASE_rator, option_CASE_rator, type_value_CASE_rator, toplevel_value_CASE_rator, LET_THM] >> rpt strip_tac >> gvs[].
works_when: Proving contradiction between lookup_global result shape and find_var_decl type
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1262-1318

## L0318 scope='global' tags=resolve_array_element,TypeError,ArrayTV
shape: resolve_array_element TypeError unreachable under typed target path through ArrayTV
pattern: resolve_array_element cannot return INR(TypeError) when subscripts at ArrayTV levels are all ValueSubscript(IntV _). target_path_step_type on Type(ArrayT ...) forces this. Prove resolve_array_element_no_type_error via ho_match_mp_tac resolve_array_element_ind; use qspec_then 0/1 for elem_offset.
works_when: Proving no-TypeError results for code paths through resolve_array_element where target_path_type constrains subscripts
evidence:
- source:semantics/vyperStateScript.sml:833-834
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:269-270

## L0320 scope='C3.5' tags=preservation,conj_tac,assign_target_preserves_state_well_typed_mutual
shape: Deriving runtime_consistent preservation for assign_targets cons from already-proved theorem
pattern: For the preservation conjunct in sound_assign_targets_cons, use: drule target_assignment_values_assignable_typed >> drule (cj 2 assign_target_preserves_state_well_typed_mutual) >> metis_tac[]. This bridges assignable→typed and then applies the second conjunct of the preservation theorem.
works_when: Proving preservation for assign_targets cons branch where the sound theorem uses target_assignment_values_assignable but the preservation theorem uses target_assignment_values_typed
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3312-3316

## L0324 scope='C3' tags=LIST_REL3,Cases_on,nil_case,cons_case,subgoal_dispatch
shape: Destructing LIST_REL3 when first list argument is a variable
pattern: When LIST_REL3 assumption has a variable first list argument `tgts`, use Cases_on `tgts` to split into nil/cons. The nil case with mismatched list lengths should be dispatched with >- before proceeding. For the cons case, gvs[LIST_REL3_def] or simp[LIST_REL3_def] >> strip_tac extracts ∃-witnesses. Never put the main proof blast (e.g. gvs[Once assign_target_def,AllCaseEqs(),...]) after Cases_on without dispatching the nil case first.
works_when: Proving theorems with LIST_REL3 assumptions where the first list argument is universally quantified and needs destructing
evidence:
- tool_output:TO_type_system_rewrite-20260515T171247Z_m10655_t001
- tool_output:TO_type_system_rewrite-20260515T171247Z_m10540_t001

## L0325 scope='C3' tags=assign_operation_matches_target_shape,TupleTargetV,boundary_lemma,Replace
shape: Proving assign_operation_matches_target_shape (TupleTargetV l) (Replace v)
pattern: Use assign_operation_matches_target_shape_Replace_from_typed boundary lemma: target_runtime_typed ∧ evaluate_type .. = SOME tv ∧ value_has_type tv v ⇒ assign_operation_matches_target_shape gv (Replace v). This handles both BaseTargetV (T) and TupleTargetV (LENGTH l = LENGTH vs via evaluate_type_TupleT_cases → values_have_types_length → target_values_runtime_typed_LIST_REL3 → LIST_REL3_LENGTHS chain). Do NOT try Cases_on `gv` inline.
works_when: Discharging assign_operation_matches_target_shape premise from LIST_REL3 witnesses in assign_target_sound_mutual IH application
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2254-2271
- tool_output:TO_type_system_rewrite-20260515T171247Z_m10647_t001

## L0327 scope='C3.5' tags=EVERY,assignable_context,rebuild,helper_lemma
shape: Rebuilding EVERY (λgv. assign_target_assignable_context cx gv st) gvs across state transition
pattern: Extract local helper: assign_target_assignable_context_rebuild_EVERY. Proves: preserves_tv cx st st' ∧ MAP FDOM st'.scopes = MAP FDOM st.scopes ∧ EVERY (λgv. assign_target_assignable_context cx gv st) gvs ⇒ EVERY (λgv. assign_target_assignable_context cx gv st') gvs. Proof by Induct_on gvs with drule_all assign_target_assignable_context_rebuild. Use metis_tac[assign_target_assignable_context_rebuild_EVERY] to discharge.
works_when: Need to rebuild EVERY assign_target_assignable_context across state transition in assign_targets cons branch
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3337-3346

## L0329 scope='C3.5' tags=assign_targets,gvs_blast,do_block,case_split
shape: Expanding assign_targets do-block after IH premises are established
pattern: In sound_assign_targets_cons: (1) Save target_assignment_values_assignable BEFORE gvs expansion. (2) Case-split assign_target cx gv (Replace v) st into INL/INR. (3) Derive runtime_consistent + no_type_error_result from head IH. (4) Rebuild tail premises. (5) THEN expand assign_targets do-block with gvs[Once assign_target_def,bind_def,...AllCaseEqs()]. (6) Apply tail IH with specific witnesses. Do NOT expand do-block before head IH application.
works_when: Proving no_type_error_result for assign_targets cons branch of assign_target_sound_mutual
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3348-3417

## L0330 scope='C3.5' tags=mutual_IH,qpat_x_assum,kall_tac,assign_target_ind
shape: Selecting correct IH from two similar universally-quantified assumptions in mutual induction resume blocks
pattern: When both head IH (∀st res st'. assign_target _ _ _ _ = _ ⟹ _) and tail IH (∀st'' res' st'''. assign_targets _ _ _ _ = _ ⟹ _) are in assumptions: (1) Kill the UNWANTED one with qpat_x_assum `∀_ _ _. assign_target _ _ _ _ = _ ==> _` kall_tac (or assign_targets pattern). (2) Then first_x_assum finds the correct remaining IH. (3) Use qspecl_then with explicit witnesses for specialization, then disch_tac/pop_assum for further specialization. This pattern works symmetrically for INL (keep tail IH) and INR (keep head IH) cases.
works_when: Mutual induction theorems where both conjuncts' IHs are in scope and first_x_assum picks the wrong one
evidence:
- tool_output:TO_type_system_rewrite-20260515T171247Z_m10775_t001
- tool_output:TO_type_system_rewrite-20260515T171247Z_m10784_t001

## L0331 scope='C3.5' tags=target_assignment_values_assignable_def,metis_tac,drule
shape: Closing tail IH application when antecedent uses unexpanded target_assignment_values_assignable
pattern: After drule matches tail IH against equation and disch_tac pops the specialized result: if the antecedent has LIST_REL3 (from expanding target_assignment_values_assignable_def) but the assumption has the UNEXPANDED target_assignment_values_assignable, use metis_tac[target_assignment_values_assignable_def, no_type_error_result_def] to bridge the gap. Do NOT expand target_assignment_values_assignable_def with simp[.] before metis — this changes the assumption shape and breaks matching.
works_when: Closing no_type_error_result goals after applying assign_targets tail IH where antecedent has target_assignment_values_assignable vs expanded LIST_REL3
evidence:
- tool_output:TO_type_system_rewrite-20260515T171247Z_m10775_t001

## L0332 scope='C3.5' tags=mutual_IH,resume,kall_tac,by_subgoal
shape: Selecting correct IH from two universally-quantified assumptions in mutual induction resume blocks
pattern: When both head IH (∀st res st'. assign_target _ _ _ _ = _ ⟹ _) and tail IH (∀st'' res' st'''. assign_targets _ _ _ _ = _ ⟹ _) are present: (1) Kill the UNWANTED one with qpat_x_assum `∀a b c. assign_targets _ _ _ _ = _ ==> _` kall_tac (or assign_target pattern). (2) Then first_x_assum finds the correct remaining IH. (3) Use qspecl_then for specialization. (4) Do NOT use by subgoal blocks - inline the tactic directly to avoid stale checkpoint interference.
works_when: Mutual induction theorems where both conjuncts' IHs are in scope and first_x_assum picks the wrong one
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10834_t001

## L0333 scope='C3.5' tags=impl_tac,metis_tac,IH_antecedent
shape: Discharging IH antecedent conjunctions after specialization
pattern: After specializing a mutual IH with qspecl_then, the antecedent is a conjunction of runtime typing facts. Do NOT use explicit conj_tac chains (risk miscounting). Instead use metis_tac with the two bridge lemmas (assign_operation_runtime_typed_Replace_from_value_has_type, assign_operation_matches_target_shape_Replace_from_typed) which handles the conjunction automatically. If metis times out, pre-derive the two bridge facts as by-subgoals BEFORE the IH specialization.
works_when: Discharging assign_target_sound_mutual IH antecedent after specialization in Resume blocks
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10834_t001

## L0334 scope='C3' tags=
shape: drule lemma after gvs substitution
pattern: When deriving facts via drule_all from a lemma that references variables (first_sub, rest_subs etc.) introduced by a prior decomp lemma, apply ALL drule calls BEFORE any gvs/Cases_on that substitutes away those variable names. gvs aggressively substitutes equations, making original variable names unavailable for subsequent drule matching.
works_when: Lemma chain where intermediate variables come from existential decomposition and then need to be consumed by another lemma before cleanup
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10877_t001

## L0335 scope='C3' tags=
shape: Monadic do-block no_TypeError proof in resume block
pattern: For heavy monadic do-block branches in Resume blocks, prove a standalone boundary lemma with minimal hypotheses FIRST, then call it from the resume via metis_tac or drule. Never inline gvs[AllCaseEqs()] expansion in the resume - it creates too many subgoals with auto-generated names and gets trapped in assumptions. The boundary lemma isolates the expansion in a clean context.
works_when: Do-block with 4+ bind layers needing AllCaseEqs expansion for TypeError dispatch
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m3377_t001

## L0336 scope='C3' tags=
shape: ArrayRef assign_target branch proof
pattern: For ArrayRef branches, use Cases_on op BEFORE expanding assign_target_def. This separates Replace/Update from AppendOp/PopOp, avoiding the pair-case (ao, final_tv) explosion that gvs[AllCaseEqs()] creates (32 goals NxM). Each operation case then uses targeted gvs expansion.
works_when: ArrayRef assignment with multiple operation types including dynamic array append/pop
evidence:
- tool_output:TO_type_system_rewrite-20260513T211025Z_m6966_t002

## L0337 scope='C3' tags=holbuild,drule_all,DISCH_THEN,metis_tac
shape: holbuild DISCH_THEN instrumentation assertion blocking drule_all/irule in new proofs
pattern: When holbuild proof_runtime.srl:749 DISCH_THEN 'predicate not true' assertion fails on drule_all/irule/drule, use metis_tac[lemma_name] instead. metis_tac handles both assumption matching and existential resolution without triggering the instrumentation check. For goals like no_type_error_result res, metis_tac[boundary_lemma] works where drule_all boundary_lemma >> simp[] fails.
works_when: Proving new theorems where drule_all/irule triggers holbuild proof_runtime DISCH_THEN assertion
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10893_t001

## L0338 scope='C3' tags=resume,preservation,forward_reference
shape: Proving runtime_consistent preservation in assign_target_sound_mutual resume blocks
pattern: In Resume blocks of assign_target_sound_mutual, use imp_res_tac (cj 1 assign_target_preserves_state_well_typed_mutual) for the preservation conjunct. Do NOT use assign_target_preserves_runtime_consistent_result (defined later, circular dependency). The earlier theorem has weaker hypotheses (no assignable_context/matches_shape needed) so the current hypotheses always suffice.
works_when: Proving runtime_consistent env cx st' in assign_target_sound_mutual resume blocks
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10927_t001

## L0339 scope='C3' tags=>-,gvs,Cases_on,variable_substitution
shape: Scoping gvs substitution after Cases_on to preserve variables
pattern: After Cases_on x (where x = SOME y or NONE), use >- gvs[] to scope gvs[] to the NONE contradiction case ONLY. This preserves y and other variables in the SOME case for subsequent lemma matching. Using >> gvs[] applies gvs to ALL subgoals including the SOME case, substituting away y and breaking drule/metas_tac matching.
works_when: Cases_on followed by gvs where the SOME case needs variables preserved for lemma application
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m10893_t001
