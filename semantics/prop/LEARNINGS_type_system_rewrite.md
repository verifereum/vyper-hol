# LEARNINGS_type_system_rewrite

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

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

## L0350 scope='global' tags=holbuild,pairarg_tac,FIRST_ABSAM,instrumentation
shape: holbuild FIRST_ABSAM instrumentation assertion from pairarg_tac
pattern: In holbuild, pairarg_tac triggers FIRST_ABSAM instrumentation assertion in new proofs. Replace with Cases_on `p` >> gvs[] (where p is the pair variable). This avoids FIRST_ABSAM and produces equivalent pair destructuring. fs[] also works to expand definitions in assumptions where gvs[] does not.
works_when: Building new theorems with holbuild where pair destructuring or definition expansion in assumptions is needed and FIRST_ABSAM/disch_then instrumentation assertions fire
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11231_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11233_t001

## L0354 scope='C3' tags=holbuild,instrumented-log,intermediate-goal-state
shape: Seeing intermediate goal state in nested THEN1 proofs
pattern: Holbuild's instrumented log only captures the TOP-LEVEL input goals for the failed fragment, not intermediate goals within nested >- chains. To see intermediate goals: insert FAIL_TAC probe right at the point where you need to inspect (not deeper in the chain). The probe message appears in the exception, and the top-level input goals show the state entering the failed fragment. For EXACT intermediate state, use suspend/Resume pattern to lift the branch to top-level.
works_when: Need to see goal state inside a nested >- chain but holbuild only shows fragment top-level input goals
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11262_t001

## L0365 scope='global' tags=API,corruption,conjunction,workaround
shape: Writing HOL4 conjunction /\ in tool call content parameters
pattern: The Anthropic API consistently corrupts /\ by stripping the backslash when it appears in replace_text/edit_lines/write_file content parameters. Produces /@, /&e, /&#92; etc. Workarounds: (1) Avoid /\ in new theorem statements entirely - use nested implications, separate single-existential theorems, or inline proof. (2) Use mp_tac + simp[definition] + strip_tac to expand definitions in goal position, getting clean Skolemized witnesses without writing /\ to file. (3) For existing theorems, copy /\ from working parts of existing file content (pre-existing /\ survives because it was written before this API limitation).
works_when: Need to write HOL4 term quotations containing /\ conjunction to .sml files via tool calls
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11333_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11275_t001

## L0369 scope='global' tags=API,unicode,conjunction,corruption
shape: Writing /\(conjunction) in SML theorem statements via tool calls
pattern: NEVER write /\ in tool call content parameters (replace_text, edit_lines, write_file). The Anthropic API consistently strips the backslash, corrupting /\ to /@, /&e, /&#92; etc. Instead: (1) use inline proof tactics that avoid /\ in new theorem text, (2) restructure as separate single-existential theorems chained via drule, (3) use mp_tac + simp + strip_tac to expand definitions in goal position getting Skolemized witnesses.
works_when: Any HOL4/SML theorem statement needing conjunction in new text written via tool calls
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11333_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11275_t001

## L0375 scope='C3' tags=var_decl_info,CASE_rator,case_expression,assumptions,simplifier
shape: var_decl_info case expression in assumptions reduced by var_decl_info_CASE_rator + var_decl_info_case_def in gvs
pattern: When a case expression on var_decl_info (or any datatype) appears in assumptions and cannot be reduced by plain gvs[] or gvs[datatype_case_def], add BOTH the _CASE_rator theorem (bridges internal CASE to external case naming) AND the _case_def theorem to gvs. The _CASE_rator converts var_decl_info_CASE x f g to var_decl_info_case f g x, then _case_def evaluates var_decl_info_case f g (Constructor args) to f args. Pattern: gvs[var_decl_info_CASE_rator, var_decl_info_case_def]. Same pattern applies to any datatype with mk_case_rator_thm_tyinfo.
works_when: Case expression on a datatype constructor stuck in assumptions after Cases_on substitution, where plain gvs fails due to internal/external name mismatch
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11735_t001
- source:semantics/vyperStateScript.sml:293-295
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1262-1318

## L0376 scope='C3' tags=mp_tac,assumption_to_goal,definition_expansion,simp
shape: Expanding definitions in assumptions via mp_tac + simp + strip_tac
pattern: When simp[def] fails to expand a definition in assumptions (because simp only rewrites the goal conclusion), use: qpat_x_assum pred mp_tac >> simp[def] >> rpt strip_tac. The mp_tac moves the assumption to the goal as antecedent, simp expands it there, and strip_tac puts expanded form back into assumptions with existentials properly introduced.
works_when: Need to expand a definition that exists only in assumptions, not the goal conclusion. Especially useful for existential-bearing definitions like assign_target_assignable_context_def.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11733_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11735_t001

## L0378 scope='C3' tags=Type_StorageVarDecl,ArrayTV,boundary_theorem,ArrayRef
shape: assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error cannot handle ArrayTV root types
pattern: The boundary theorem assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error requires (!elem_tv bd. root_tv <> ArrayTV elem_tv bd) as premise. When vt = Type (ArrayT elem_t bd), the runtime root type IS ArrayTV and lookup_global returns ArrayRef (not Value). This premise is NOT derivable from wrapper assumptions. Fix: either modify the boundary theorem to dispatch ArrayRef branch to assign_target_TopLevelVar_ArrayRef_branch_no_type_error instead of contradiction, or case-split root_tv in the wrapper.
works_when: Calling assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error from a wrapper where vt = Type t and t could be ArrayT
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11745_t002

## L0380 scope='C3' tags=type_value,ArrayTV,ArrayRef,TopLevelVar,dispatch
shape: Dispatch Type-typed TopLevelVar by root type_value to correct boundary theorem
pattern: When vt = Type t and find_var_decl returns StorageVarDecl, the root evaluate_type result determines which boundary theorem: (1) ArrayTV -> assign_target_TopLevelVar_ArrayRef_branch_no_type_error via lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef. (2) Non-ArrayTV -> assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error. Key dispatch: Cases_on the evaluated type_value after extracting IS_SOME witnesses.
works_when: Proving TopLevelVar no_type_error wrapper where vt = Type t and root type could be ArrayTV
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3012-3136
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2511-2523

## L0384 scope='C3' tags=mp_tac,definition_expansion,assumptions,assign_target_assignable_context
shape: Expanding definitions in assumptions via mp_tac + simp + strip_tac
pattern: When simp cannot expand a definition that exists only in assumptions, use: qpat_x_assum pred mp_tac >> simp[def] >> rpt strip_tac. This moves the assumption to the goal as antecedent, expands it there with simp, and strip_tac puts expanded form back into assumptions with existentials properly introduced. Especially critical for assign_target_assignable_context_def which has existential quantifiers.
works_when: Need to expand an existential-bearing definition that exists only in assumptions, not the goal conclusion
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11733_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11735_t001

## L0386 scope='C3' tags=contradiction,var_decl_info,top_level,FLOOKUP
shape: TopLevelVar FLOOKUP type vs find_var_decl constructor contradiction pattern
pattern: When FLOOKUP gives one type constructor (e.g. Type t) but find_var_decl_by_num gives a different var_decl_info constructor (e.g. HashMapVarDecl): prove F via expanding runtime_consistent/env_consistent/env_context_consistent which connects FLOOKUP types to find_var_decl constructors. Use rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >> metis_tac[] pattern (see top_level_Type_not_hashmap_decl at line 1366). For the symmetric case (HashMapT with StorageVarDecl), prove top_level_HashMapT_not_storage_decl the same way.
works_when: Contradicting TopLevelVar type_value with var_decl_info constructor mismatch
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1366-1375

## L0387 scope='C3' tags=type_value_distinct,ArrayTV,boundary_theorem,Cases_on
shape: Dispatching root type_value to correct boundary theorem via Cases_on after IS_SOME extraction
pattern: After extracting evaluate_type witnesses via Cases_on option (NONE contradicts IS_SOME, SOME gives type_value x), use Cases_on x to split by type_value constructor. For non-ArrayTV (BaseTV/TupleTV/StructTV/FlagTV/NoneTV): use assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error + type_value_distinct. For ArrayTV: use assign_target_TopLevelVar_ArrayRef_branch_no_type_error + lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef. The type_value_distinct lemma is required to prove root_tv <> ArrayTV for non-ArrayTV constructors.
works_when: Proving TopLevelVar no_TypeError wrapper where vt=Type t and root type could be ArrayTV (dispatching to different boundary theorems)
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3012-3136

## L0388 scope='C3' tags=contradiction,HashMapT,StorageVarDecl,var_decl_info,FLOOKUP
shape: Contradict HashMapT vt with StorageVarDecl find_var_decl_by_num result
pattern: When FLOOKUP = SOME (HashMapT kt vt) but find_var_decl returns SOME (StorageVarDecl ...): prove top_level_HashMapT_not_storage_decl (modeled on top_level_Type_not_hashmap_decl) using rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >> metis_tac[]. The lemma states: runtime_consistent + FLOOKUP=SOME(HashMapT kt vt) + get_module_code + find_var_decl=SOME(StorageVarDecl ...) => F. NEVER use optionTheory.option showdown (corrupted Unicode).
works_when: Contradicting HashMapT type_value with StorageVarDecl declaration in TopLevelVar branch
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1366-1375

## L0389 scope='C3' tags=type_value_distinct,ArrayTV,boundary_theorem,TopLevelVar,dispatch
shape: Dispatching root type_value to correct boundary theorem via Cases_on + type_value_distinct
pattern: After extracting evaluate_type witnesses via Cases_on option, use Cases_on x to split by type_value constructor. For non-ArrayTV (BaseTV/TupleTV/StructTV/FlagTV/NoneTV): add type_value_distinct to metis_tac[assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error, type_value_distinct] - the boundary theorem requires (!elem_tv bd. root_tv <> ArrayTV elem_tv bd) which type_value_distinct proves for each non-ArrayTV constructor. For ArrayTV: use assign_target_TopLevelVar_ArrayRef_branch_no_type_error + lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef.
works_when: Proving TopLevelVar no_TypeError wrapper where vt=Type t, root type could be ArrayTV, dispatching to different boundary theorems after Cases_on type_value
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3012-3136

## L0392 scope='C3' tags=contradiction,HashMapT,StorageVarDecl,FLOOKUP,==>_chain
shape: Contradict HashMapT vt with StorageVarDecl via top_level_HashMapT_not_storage_decl
pattern: When FLOOKUP gives HashMapT but find_var_decl gives StorageVarDecl, use top_level_HashMapT_not_storage_decl (line 3258): ==> chain format with rpt strip_tac >> drule_all top_level_HashMap_decl >> strip_tac >> gvs[]. This avoids the metis timeout from the full env_expansion. NEVER use optionTheory.option showdown (corrupted Unicode).
works_when: Contradicting HashMapT type_value with StorageVarDecl declaration in TopLevelVar branch
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3258-3268
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1366-1375

## L0400 scope='C3' tags=irule,boundary_theorem,wrapper_lemma,variable_bridging,diagnostic
shape: Using irule on boundary theorem in wrapper lemma to diagnose variable-name mismatches
pattern: When a wrapper lemma calls a boundary theorem with many premises, but expanding an opaque predicate via mp_tac+simp+strip_tac changes variable names in assumptions breaking metis_tac, use irule boundary_theorem FIRST. irule matches the conclusion no_type_error_result and creates one subgoal per antecedent. Derive each subgoal individually with by metis_tac. This avoids variable-name mismatch because each subgoal is checked independently. Save critical equations like env.type_defs=get_tenv cx with pop_assum $ mk_asm 'etd' BEFORE any fs/gvs that might eliminate them; restore with asm 'etd' assume_tac after.
works_when: Proving wrapper/integration lemma that calls multi-premise boundary theorem, where expanding opaque hypotheses changes variable names. Especially when metis_tac fails with FOL_FIND after fs/gvs expansion.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11950_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3270-3318

## L0401 scope='C3' tags=adapter_bridge,==>_chain,single_witness,assignable_context,API_safe
shape: Bridge lemma with ==> chain single-witness conclusions to avoid /\ API corruption
pattern: When expanding assign_target_assignable_context via mp_tac+simp changes variable names breaking metis_tac, write SEPARATE single-witness bridge lemmas whose conclusions each output exactly ONE existential fact as ==> chain: e.g., `assign_target_assignable_context cx (BaseTargetV (TopLevelVar src n) sbs) st ==> env.type_defs = get_tenv cx ==> (?code. get_module_code cx src = SOME code)`. Each lemma does its own internal mp_tac+simp+strip_tac expansion, confining damage. Consumer applies each with drule_all >> strip_tac individually, building up clean witnesses. NEVER use /\ in lemma conclusions written via tool calls (API corrupts it).
works_when: Need to extract existential witnesses from complex definition where /\ in conclusions gets API-corrupted and fs expansion in the main proof body breaks metis matching
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11275_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11333_t001

## L0402 scope='C3' tags=env.type_defs,get_tenv_cx,fs,gvs,equation_loss,labelled_assumptions
shape: Preventing fs/gvs from eliminating env.type_defs=get_tenv cx during proof expansion
pattern: After mp_tac + simp[assign_target_assignable_context_def] + strip_tac + PairCases_on + gvs expansion, fs[] at line 3301 can rewrite env.type_defs to get_tenv cx everywhere, eliminating the equation. Downstream boundary theorems that need env.type_defs = get_tenv cx as a separate premise then fail. FIX: save the equation BEFORE any gvs/fs with `pop_assum $ mk_asm 'etd'` using markerLib; restore after with `asm 'etd' assume_tac`. Alternatively re-derive from runtime_consistent_def + env_consistent_def + env_context_consistent_def.
works_when: Proving wrapper lemmas needing env.type_defs=get_tenv cx as boundary theorem premise after definition expansion steps that might eliminate it
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11981_t002
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3301

## L0403 scope='C3.1' tags=irule,boundary_theorem,diagnostic,variable_bridging
shape: Using irule on multi-premise boundary theorem to diagnose premise matching failures
pattern: When metis_tac fails after expanding opaque hypotheses (assign_target_assignable_context) because variable names change, use irule boundary_theorem FIRST. irule matches the conclusion and creates one subgoal per antecedent, revealing exactly which premises are missing/mismatched. Fill each subgoal individually with simp[]/goal_assum drule_all/asm assume_tac. Save critical equations like env.type_defs=get_tenv cx BEFORE any fs/gvs with pop_assum $ mk_asm 'label'; restore with asm 'label' assume_tac after.
works_when: Proving wrapper/integration lemmas calling multi-premise boundary theorems after opaque hypothesis expansion that renames variables
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12034_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227

## L0404 scope='C3.1' tags=fs,elimination,env.type_defs,labelled_assumptions
shape: Preventing fs/gvs from eliminating env.type_defs=get_tenv cx during assignable_context expansion
pattern: After mp_tac + simp[assign_target_assignable_context_def] + strip_tac + PairCases_on + gvs, the fs[] that substitutes t'=t may also eliminate env.type_defs=get_tenv cx by rewriting it everywhere. Downstream boundary theorems need env.type_defs=get_tenv cx as a separate premise. FIX: Before any fs/gvs that substitutes, save the equation with pop_assum $ mk_asm 'etd' using markerLib. After fs, restore with asm 'etd' assume_tac. Alternatively, re-derive from runtime_consistent_def + env_consistent_def after fs.
works_when: Proving wrapper lemmas needing env.type_defs=get_tenv cx as boundary theorem premise after definition expansion steps that might eliminate it
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11981_t002

## L0405 scope='global' tags=API,conjunction,corruption,workaround
shape: NEVER write /\ in new theorem statements via tool calls - use alternative proof structures
pattern: The Anthropic API consistently strips the backslash from /\ when writing via replace_text/edit_lines/write_file, corrupting /\ to /@, /&e, etc. Workarounds: (1) Use irule in proof body instead of adapter lemmas with /\ conclusions. (2) Split into separate single-existential/drive lemmas. (3) Use inline proof expansion (mp_tac+simp+strip_tac) to get Skolemized witnesses without writing /\ to file. (4) Copy /\ from EXISTING working file content (pre-existing /\ survived before this API limitation).
works_when: Any HOL4/SML theorem statement or term quotation needing conjunction in new text written via tool calls
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11333_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11275_t001

## L0406 scope='C3.1' tags=holbuild,nested_proof,goal_state_visibility,local_lemma,suspend
shape: Nested >- chain failures show only top-level goals in holbuild instrumented log
pattern: When a proof fails inside a deeply nested >- chain and holbuild only shows the outermost input goals (not the inner state after expansion), extract the failing branch as a SEPARATE [local] Theorem. This makes holbuild show the full goal state at the failure point. Alternatively, use suspend/Resume to lift the branch to a top-level block. This is the single最重要的 debugging technique for nested-prefixed checkpoint proofs.
works_when: Proof fails inside nested Cases_on >- chains, holbuild shows only fragment-level input goals, and you need to see assumption names and conclusion after intermediate expansion steps
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12043_t002

## L0407 scope='C3.1' tags=irule,boundary_theorem,witness_extraction,assignable_context
shape: irule boundary theorem after witness extraction from assignable_context
pattern: After expanding assign_target_assignable_context via mp_tac+simp+strip_tac+PairCases_on+Cases_on: (1) Save env.type_defs=get_tenv cx with pop_assum $ mk_asm 'etd' BEFORE gvs that might eliminate it. (2) Extract IS_SOME witnesses via Cases_on option (NONE contradicts, SOME gives witness). (3) Derive well_formed_type_value from evaluate_type_well_formed_type_value. (4) Derive typ=t from top_level_Type_storage_decl. (5) Re-derive env.type_defs=get_tenv cx if eliminated. (6) Cases_on root_tv, irule correct boundary theorem, fill premises. NEVER rely on goal_assum drule_all alone - derive intermediate facts first.
works_when: Proving TopLevelVar no-TypeError wrappers that consume assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error or assign_target_TopLevelVar_ArrayRef_branch_no_type_error after context expansion
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3012-3136
- source:semantics/prop/vyperTypeStatePreservationScript.sml:949-966

## L0408 scope='C3.1' tags=local_lemma,holbuild,goal_state,nested_proof,Cases_on
shape: Making intermediate goal state visible in holbuild for nested case-analysis proofs
pattern: When a proof fails inside a nested >- chain (Cases_on >- branch >- sub-branch...) and holbuild only shows the outermost fragment input goals, EXTRACT THE FAILING BRANCH AS A SEPARATE [local] Theorem. This makes holbuild show the full goal state (assumptions + conclusion) at the failure point. The separate theorem can be called from the main theorem via metis_tac after it's proved. This is the single most important debugging technique for nested-prefixed checkpoint proofs.
works_when: Proof fails inside nested Cases_on >- chain, holbuild shows only fragment-level input goals, and you need to see assumption names and conclusion after intermediate expansion steps. Especially useful after mp_tac+simp+strip_tac+PairCases_on sequences that change variable names.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12093_t001

## L0409 scope='C3.1' tags=irule,boundary_theorem,witness_extraction,assignable_context
shape: Proving TopLevelVar Type no-TypeError after extracting assignable_context witnesses
pattern: After expanding assign_target_assignable_context via mp_tac+simp+strip_tac+PairCases_on+Cases_on: (1) Use metis_tac[IS_SOME_DEF] for NONE branches (not gvs[]). (2) Derive t'=t by metis_tac[top_level_Type_storage_decl] + fs[] (variable is t' not typ). (3) Derive well_formed_type_value by metis_tac[evaluate_type_well_formed_type_value]. (4) Cases_on x (type_value). (5) ArrayTV: irule assign_target_TopLevelVar_ArrayRef_branch_no_type_error + metis_tac[lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef]. (6) Non-ArrayTV: irule assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error + simp[type_value_distinct]. (7) Check env.type_defs=get_tenv cx survives fs[] - save with mk_asm if needed.
works_when: Proving TopLevelVar Type no-TypeError wrapper that consumes assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error or assign_target_TopLevelVar_ArrayRef_branch_no_type_error after context expansion
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12093_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3012-3026

## L0410 scope='C3.1' tags=IS_SOME,existential_witness,option
shape: IS_SOME (f args)
pattern: Use gvs[optionTheory.IS_SOME_EXISTS] to resolve IS_SOME hypotheses into concrete witnesses. Never use Cases_on on the option + metis_tac[IS_SOME_DEF] - gvs already resolves IS_SOME NONE contradictions leaving no subgoal for metis. This pattern is established in vyperTypeEnvPreservationScript.sml (8+ uses).
works_when: Goal assumptions contain IS_SOME (f args) where f returns an option type, and you need concrete SOME witnesses.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12175_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12121_t001

## L0411 scope='C3.1' tags=irule,boundary_theorem,intermediate_step,variable_mismatch
shape: irule boundary_thm where assumption variable names differ from theorem variable names
pattern: When irule+goal_assum fails due to variable name mismatches between assumptions and boundary theorem: prove a small intermediate fact first (e.g. lookup_global returns specific constructor), then use metis_tac[boundary_thm]. This two-step approach avoids the existential unification problem. For the ArrayTV branch: (1) prove lookup_global fact via metis_tac[lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef], (2) metis_tac[assign_target_TopLevelVar_ArrayRef_branch_no_type_error].
works_when: irule creates a large existential conjunction goal where assumption variable names from gvs[IS_SOME_EXISTS] differ from boundary theorem variable names.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12175_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12198_t001

## L0412 scope='C3.1' tags=type_value,constructor_order,Cases_on
shape: Cases_on `x` where x : type_value
pattern: type_value datatype constructor order (from vyperValueScript.sml): BaseTV, TupleTV, ArrayTV, StructTV, FlagTV, NoneTV. Branch labels must match this order for >- dispatch. Not ArrayTV-first as sometimes assumed.
works_when: Any case split on type_value via Cases_on
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12172_t001

## L0413 scope='C3' tags=variable_name_bridging,context_expansion,injectivity,top_level_HashMap_decl,metis
shape: find_var_decl_by_num witnesses from context expansion differ from FLOOKUP type params (kt, vt)
pattern: After expanding assign_target_assignable_context via mp_tac+simp+strip_tac+PairCases_on+Cases_on+gvs[IS_SOME_EXISTS]: the find_var_decl witnesses get auto-generated names (b, t, v, p1) different from FLOOKUP params (kt, vt). For HashMapT: use drule_all top_level_HashMap_decl to get a consistent find_var_decl with matching kt/vt, then prove variable equalities via metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ, var_decl_info_11], then fs[] to substitute, then metis_tac[boundary_theorem]. For Type: use top_level_Type_storage_decl similarly (but it was simpler since the boundary theorem doesn't tie find_var_decl type args to FLOOKUP args directly).
works_when: Proving TopLevelVar no-TypeError wrappers after assign_target_assignable_context expansion where find_var_decl_by_num witnesses have different variable names from the vtype in FLOOKUP
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12265_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12256_t001

## L0414 scope='C3' tags=is_transient,boolean_equivalence,fs_substitution
shape: is_transient <=> b after context expansion needs explicit equality derivation
pattern: After drule_all top_level_HashMap_decl + strip_tac introduces is_transient' from the lemma, while context expansion has b. The resulting is_transient' <=> b equivalence (boolean bi-implication) gets simplified by fs[] to is_transient' = b AFTER proving the variable equalities t=kt and v=vt. But metis cannot use <=> to rewrite function arguments - it needs the actual equality is_transient' = b. Derive it explicitly: `is_transient' = b` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ, var_decl_info_11, EQ_SYM_EQ], then fs[] handles the substitution.
works_when: Boolean equivalence (⇔) between two variables needs to become equality (=) for metis to use them interchangeably in function arguments
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12261_t001

## L0415 scope='C5' tags=bridge_lemma,assign_operation_matches_target_shape,Replace,target_runtime_typed
shape: Deriving assign_operation_matches_target_shape gv (Replace v) from target_runtime_typed + evaluate_type + value_has_type
pattern: assign_operation_matches_target_shape_Replace_from_typed already exists in vyperTypeStatePreservationScript.sml (line 2254): target_runtime_typed env cx st tgt ty gv + evaluate_type env.type_defs ty = SOME tv + value_has_type tv v => assign_operation_matches_target_shape gv (Replace v). For statement branches: derive target_runtime_typed from eval_target soundness + runtime_consistent, then drule this lemma. For non-Replace operations, unfold assign_operation_matches_target_shape_def to verify BaseTargetV always true.
works_when: Statement assignment branches need assign_operation_matches_target_shape premise for C3 assign_target_sound_mutual
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2254-2271

## L0417 scope='C5' tags=assign_branch_cheats,vyperTypeStmtSoundnessScript,bridge_lemma_placement
shape: 8 cheats in Assign branch all need assign_operation_matches_target_shape + assign_target_assignable_context
pattern: In eval_all_type_sound_mutual[Assign] (lines 667-831): there are 8 cheat locations at lines 698, 699, 720, 721, 743, 744, 766, 767. ALL are `assign_operation_matches_target_shape gv (Replace v) by cheat` and `assign_target_assignable_context cx gv st3 by cheat`. After proving the C5 bridge lemmas, these become drule/irule applications. The existing assign_operation_matches_target_shape_Replace_from_typed handles the shape; the assignable_context bridge lemma (to be proved) handles the context. Place bridge lemmas in vyperTypeStmtSoundnessScript.sml near the assignment cases.
works_when: Replacing cheats in eval_all_type_sound_mutual[Assign] with proved bridge lemma calls
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:667-831

## L0419 scope='C5' tags=assign_operation_matches_target_shape,Replace,BaseTargetV,bridge_lemma
shape: assign_operation_matches_target_shape gv (Replace v) for BaseTargetV is trivially T
pattern: assign_operation_matches_target_shape_BaseTargetV (already proved in vyperTypeAssignSoundnessScript.sml line 370) proves this is T for ALL BaseTargetV cases. Only TupleTargetV needs value alignment. So for Assign branch with gv from eval_target (which gives BaseTargetV for BaseTarget and TupleTargetV for TupleTarget), use assign_operation_matches_target_shape_BaseTargetV for BaseTargetV case, and assign_operation_matches_target_shape_Replace_from_typed for TupleTargetV case.
works_when: Replacing assign_operation_matches_target_shape cheats in statement assignment branches
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:370-374
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2254-2271

## L0420 scope='global' tags=Unicode,conjunction,tool_calls,HOL4_syntax
shape: Writing /\ in HOL4 theorem statements via tool calls gets corrupted
pattern: NEVER write /\ in new theorem statements via tool calls. Use ==> implication chains instead: 'P ==> Q ==> R' instead of 'P /\ Q ==> R'. Existing source files use /\ fine (it's ASCII), but tool call content parameters corrupt it. This applies to ALL new theorem and Definition statements written through replace_text/append_file/write_file.
works_when: Writing new HOL4 theorem/definition statements through tool calls
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12405_t001

## L0421 scope='C5' tags=TopLevelVar,execution_extraction,contrapositive,lookup_global,bind_def
shape: Contrapositive extraction from assign_target execution for TopLevelVar
pattern: For TopLevelVar: assign_target_def starts with bind (lookup_global cx src n st) continuation. So: (1) get_module_code NONE => lookup_global TypeError => bind passes INR through => assign_target TypeError. Contrapositive: assign_target no-TypeError => get_module_code SOME. (2) lookup_global INR => assign_target INR. Contrapositive: assign_target INL => lookup_global INL. Each extraction lemma expands ONLY lookup_global_def or assign_target_def's FIRST bind step, not the whole definition.
works_when: Deriving TopLevelVar context premises (get_module_code, find_var_decl, etc.) from assign_target execution success or no-TypeError result
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:389-408
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:413-423
- source:semantics/vyperStateScript.sml:873-876

## L0422 scope='C5' tags=location_runtime_typed,TopLevelVar,target_runtime_typed,bridge_lemma
shape: location_runtime_typed for TopLevelVar may provide assignable_context facts directly
pattern: target_runtime_typed env cx st (BaseTarget bt) (BaseTargetV loc sbs) includes location_runtime_typed env cx st loc vt. For TopLevelVar, location_runtime_typed_def (at vyperTypeExprSoundnessScript.sml:258) likely provides FLOOKUP env.toplevel_vtypes = SOME vt and related module/declaration facts. If so, assign_target_assignable_context can be derived from target_runtime_typed + runtime_consistent WITHOUT expanding assign_target_def at all. MUST READ THIS DEFINITION FIRST next session.
works_when: Writing bridge lemma: target_runtime_typed + runtime_consistent => assign_target_assignable_context for any target value constructor
evidence:
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:258
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:662-666

## L0423 scope='C5' tags=mutual_theorem,weaker_premises,avoid_context_bridge
shape: assign_target preservation in statement branches
pattern: Use assign_target_preserves_state_well_typed_mutual directly (cj 1 for single target) instead of individual corollaries like assign_target_preserves_runtime_consistent. The mutual theorem has WEAKER premises: only runtime_consistent + target_runtime_typed + assign_operation_runtime_typed. The individual corollaries add assign_operation_matches_target_shape + assign_target_assignable_context which are hard to derive from static typing alone. For no-TypeError, assign_target_no_type_error only needs assign_target_assignable, not assign_target_assignable_context.
works_when: Proving statement-level assignment branches (Assign, AnnAssign, AugAssign, Append) where runtime_consistent and target_runtime_typed are available from expression/target evaluation soundness.
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1056-1062
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:313-336

## L0424 scope='global' tags=existential,PULL_EXISTS,rename1,API_corruption
shape: Proving subgoals with existentially-quantified variables from assumptions
pattern: When an assumption like expr_runtime_typed env e tvl contains ?tv. evaluate_type ... = SOME tv /\ ..., do NOT try to prove evaluate_type ... = SOME tv as a subgoal with a free variable tv. Instead: gvs[expr_runtime_typed_def, PULL_EXISTS] to expose the existential, then rename1 to give the witness a stable name. This avoids the API /\ corruption issue and avoids type-mismatch failures from free vs bound variables.
works_when: Assumptions contain existentially quantified facts that need to be unfolded and the witness variables need stable names for subsequent drule/irule calls.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12630_t001

## L0425 scope='C5' tags=assignable_context,TopLevelVar,get_module_code,circular_dependency
shape: Deriving assign_target_assignable_context for TopLevelVar
pattern: assign_target_assignable_context for TopLevelVar requires get_module_code + find_var_decl_by_num + IS_SOME facts. runtime_consistent does NOT provide get_module_code for TopLevelVar. env_context_consistent only provides declaration facts CONDITIONED on get_module_code=SOME. This creates a gap: you cannot derive context from runtime_consistent alone. Two solutions: (1) extract from execution success (assign_target returns INL implies get_module_code=SOME), or (2) use the mutual theorem which doesn't need context at all.
works_when: Need to understand why assign_target_assignable_context is hard to derive and why the mutual theorem is the better path.
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:713-731
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:258-259

## L0426 scope='C5' tags=metis_tac,assign_target,mutual_theorem,runtime_consistent
shape: Proving runtime_consistent from assign_target_preserves_state_well_typed_mutual in statement branches
pattern: To derive runtime_consistent env cx st' from assign_target_preserves_state_well_typed_mutual: use `runtime_consistent env cx st' by metis_tac[cj 1 assign_target_preserves_state_well_typed_mutual, assign_operation_runtime_typed_def, value_runtime_typed_def]`. Then gvs[runtime_consistent_def] to decompose. metis handles universal instantiation and definition expansion automatically, avoiding drule/irule matching failures.
works_when: Statement assignment branches where runtime_consistent and target_runtime_typed are available from expression/target evaluation soundness
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12689_t001

## L0427 scope='C5' tags=metis_tac,materialise,value_has_type
shape: Proving value_has_type from materialise_preserves_value_type with multiple state_well_typed assumptions
pattern: When proving value_has_type tv v from materialise_preserves_value_type, drule fails because multiple state_well_typed assumptions exist and drule matches the wrong one. Fix: metis_tac[materialise_preserves_value_type, evaluate_type_well_formed_type_value]. metis resolves correct assumption matching.
works_when: Multiple state_well_typed assumptions in goal (st, st1, st2) cause drule to match wrong one for materialise theorem
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12640_t002

## L0429 scope='C5' tags=assignable_type,NoneT,NoneTV,materialise
shape: Deriving tv <> NoneTV from assignable_type for materialise INR case
pattern: When materialise returns INR(Error(TypeError)), need tv <> NoneTV. Chain: drule assignable_type_not_NoneT (gets expr_type e <> NoneT), then drule evaluate_type_not_NoneT_imp_not_NoneTV (gets tv <> NoneTV).
works_when: Materialise INR branch where TypeError could arise from NoneTV value needing to be ruled out
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12707_t001

## L0430 scope='C7' tags=switch_BoolV,assert,raise,state_preservation,metis_tac
shape: Proving state preservation through switch_BoolV with concrete continuations
pattern: For switch_BoolV tv (return ()) (raise exn) st = (res,st'): expand evaluate_def+bind_def with AllCaseEqs(), then use `metis_tac[switch_BoolV_state, return_state, raise_state]` to derive `st' = s''`. Then gvs[] to propagate state preservation. For no-TypeError: use switch_BoolV_assert_no_type_error (drule) or Cases_on b after drule toplevel_value_typed_BoolTV. NEVER use irule switch_BoolV_state - it has universally-quantified continuations that don't match concrete return()/raise().
works_when: Assert/AssertUnreachable/any branch using switch_BoolV with concrete monadic continuations where state preservation and no-TypeError are needed
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12793_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:518-542

## L0431 scope='C7' tags=RaiseReason,get_Value,dest_StringV,lift_option_type,boundary_lemma
shape: Proving RaiseReason soundness through get_Value + dest_StringV + raise pipeline
pattern: RaiseReason evaluates expr to StringV-typed value, then get_Value, dest_StringV, lift_option_type, raise AssertException. Use existing boundary lemmas: (1) drule get_Value_String_no_type_error to close INR branches from get_Value expansion; (2) drule toplevel_value_typed_StringTV to get StringV witness; (3) imp_res_tac get_Value_state/lift_option_type_state/raise_state for state preservation. Do NOT use AllCaseEqs() on get_Value/lift_option_type - it creates impossible branches. Use Cases_on result instead.
works_when: RaiseReason branch and any branch with get_Value + dest_StringV pipeline under StringT typing
evidence:
- source:semantics/vyperInterpreterScript.sml:830-834
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:55-65
- source:semantics/prop/vyperTypeValuesScript.sml:47-52

## L0433 scope='C7' tags=RaiseReason,get_Value,lift_option_type,boundary_lemma
shape: RaiseReason/AssertReason proof pattern: imp_res_tac state + drule boundary lemma
pattern: For statement branches with monadic pipelines (get_Value, switch_BoolV, lift_option_type): (1) Use AllCaseEqs ONLY on evaluate_def for the overall branch structure. (2) After getting runtime-typed toplevel values, use imp_res_tac for state preservation (get_Value_state, lift_option_type_state, raise_state, switch_BoolV_state). (3) Use drule for no-TypeError boundary lemmas (get_Value_String_no_type_error, switch_BoolV_assert_no_type_error). (4) rw[] to normalize state equations. (5) gvs[] for definition cleanup. Do NOT use AllCaseEqs on get_Value/lift_option_type/switch_BoolV - creates impossible branches.
works_when: Statement branches with monadic pipeline: eval_expr -> get_Value/switch_BoolV/lift_option_type -> raise/return
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12873_t001

## L0434 scope='C4' tags=assign_target_sound_mutual,corollary,EVERY,arg_order
shape: Projecting no_type_error_result from assign_target_sound_mutual cj 1/cj 2
pattern: Use imp_res_tac (cj N assign_target_sound_mutual) >> gvs[] to project no_type_error_result from C3. For EVERY premises, the arg order is assign_target_assignable_context cx gv st (NOT cx st gv). Use EVERY (\gv. assign_target_assignable_context cx gv st) gvs matching C3 line 2290 exactly. For update/append wrappers, build assign_operation_runtime_typed from component facts first (well_typed_binop+value_runtime_typed for Update; evaluate_type+value_has_type for AppendOp).
works_when: Proving C4 wrapper theorems as projections from C3 assign_target_sound_mutual
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:313-376
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2274-2291

## L0435 scope='C5' tags=bridge_lemma,assign_target_assignable_context,TopLevelVar,get_module_code,gap
shape: Deriving assign_target_assignable_context for TopLevelVar needs get_module_code which is NOT derivable from runtime_consistent + target_runtime_typed
pattern: CRITICAL GAP: assign_target_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) st requires get_module_code cx src = SOME code + find_var_decl_by_num + IS_SOME evaluate_type/lookup_var_slot_from_layout. But target_runtime_typed for TopLevelVar only provides FLOOKUP env.toplevel_vtypes = SOME vt (not get_module_code). env_context_consistent uses get_module_code as antecedent only. RESOLUTION OPTIONS: (A) Strengthen env_context_consistent with FLOOKUP env.toplevel_vtypes (src,id) = SOME vt => get_module_code cx src = SOME code, (B) Extract get_module_code from execution result in statement branch proof via case analysis on assign_target result, (C) Prove direct execution-level no-TypeError for TopLevelVar. For ScopedVar: assign_target_assignable_context simplifies to assign_target_assignable (via eval_target_assignable) /\ T. For ImmutableVar: assign_target_assignable and context are both T.
works_when: Proving bridge lemmas for assign_target_assignable_context in statement assignment branches
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:949-966
- source:semantics/prop/vyperTypeSystemScript.sml:713-731
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:258-259

## L0436 scope='C5' tags=assign_operation_matches_target_shape,bridge_lemma,Replace
shape: assign_operation_matches_target_shape gv (Replace v) for BaseTargetV is trivially T
pattern: assign_operation_matches_target_shape_BaseTargetV (vyperTypeAssignSoundnessScript.sml:381) proves this is T for ALL BaseTargetV cases. For TupleTargetV, assign_operation_matches_target_shape_Replace_TupleTargetV requires LENGTH gvs = LENGTH vs. In Assign branch, gv comes from eval_target which returns BaseTargetV for BaseTarget and TupleTargetV for TupleTarget. Use assign_operation_matches_target_shape_Replace_from_typed (vyperTypeStatePreservationScript.sml:2254) for the TupleTargetV case.
works_when: Deriving assign_operation_matches_target_shape gv (Replace v) for statement assignment branches
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:381-393
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2254-2271

## L0437 scope='C4' tags=EVERY,arg_order,assign_target_assignable_context
shape: EVERY for assign_target_assignable_context must use lambda form
pattern: assign_target_assignable_context takes args (cx, gv, st) in that order. EVERY (assign_target_assignable_context cx st) gvs is WRONG type error because cx st is not a valid prefix - st is evaluation_state not assignment_value. Must use EVERY (\gv. assign_target_assignable_context cx gv st) gvs matching C3 line 2290. Both \ syntax and lambda character work in HOL4 definitions.
works_when: Writing theorem statements with EVERY over assign_target_assignable_context
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2290
