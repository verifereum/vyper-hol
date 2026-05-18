# LEARNINGS_type_system_rewrite

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

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

## L0424 scope='global' tags=existential,PULL_EXISTS,rename1,API_corruption
shape: Proving subgoals with existentially-quantified variables from assumptions
pattern: When an assumption like expr_runtime_typed env e tvl contains ?tv. evaluate_type ... = SOME tv /\ ..., do NOT try to prove evaluate_type ... = SOME tv as a subgoal with a free variable tv. Instead: gvs[expr_runtime_typed_def, PULL_EXISTS] to expose the existential, then rename1 to give the witness a stable name. This avoids the API /\ corruption issue and avoids type-mismatch failures from free vs bound variables.
works_when: Assumptions contain existentially quantified facts that need to be unfolded and the witness variables need stable names for subsequent drule/irule calls.
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m12630_t001

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

## L0445 scope='C3' tags=TopLevelVar,Type,ArrayTV,dispatch,boundary_theorem,root_type_value
shape: Dispatching TopLevelVar Type branch by root type_value to correct boundary theorem
pattern: When vt = Type t with StorageVarDecl: after extracting IS_SOME evaluate_type witnesses into SOME root_tv, dispatch by root_tv constructor. ArrayTV -> assign_target_TopLevelVar_ArrayRef_branch_no_type_error + lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef. Non-ArrayTV (BaseTV/TupleTV/StructTV/FlagTV/NoneTV) -> assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error + type_value_distinct (proves root_tv <> ArrayTV elem_tv bd premise). This dispatch is needed because the Value-branch boundary theorem requires non-ArrayTV root while the ArrayRef branch handles the ArrayTV case.
works_when: Proving TopLevelVar no_type_error where vt=Type t and root type could be either ArrayTV or non-ArrayTV
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3184-3227
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3012-3136

## L0446 scope='C3' tags=TopLevelVar,HashMapT,assignable_context,irule,boundary_theorem
shape: Completing HashMapT+HashMapVarDecl branch of sound_TopLevelVar using irule on boundary theorem
pattern: For the HashMapT kt vt' + HashMapVarDecl sub-branch in sound_TopLevelVar: after deriving well_formed_vtype and assign_target_assignable via gvs, use irule top_level_HashMapRef_assign_no_type_error then goal_assum drule_all >> simp[] to fill remaining premises. The boundary theorem needs: runtime_consistent, FLOOKUP, target_path_type, assignable_type, assign_operation_runtime_typed, assign_operation_matches_target_shape, assign_target_assignable, well_formed_vtype, get_module_code, find_var_decl_by_num, lookup_var_slot_from_layout. Most are already in assumptions or derivable. If metis_tac fails due to variable-name mismatch after expansion, use irule to diagnose which premise is missing.
works_when: Proving HashMapT TopLevelVar no_type_error branch in sound_TopLevelVar Resume proof
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3243-3270
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3289-3299

## L0447 scope='C3' tags=TopLevelVar,assignable_context,variable_name_bridging,adapter_lemma,drule
shape: Inline expansion of assign_target_assignable_context in Resume proofs produces unstable auto-generated variable names after Cases_on + gvs
pattern: After expanding assign_target_assignable_context_def inline in the sound_TopLevelVar Resume proof via mp_tac+simp+strip_tac, then Cases_on on var_decl_info followed by gvs[], the constructor parameters get auto-generated names (b', t', v3, v4) that don't match universally-quantified variable names in theorems like top_level_Type_storage_decl. Two solutions: (1) Add [local] adapter theorems (PLAN C3.1.1/C3.1.2) that extract stable witnesses (code, is_transient, typ, id_str, slot) from assign_target_assignable_context, then drule on those in the Resume proof. (2) After Cases_on vi >> gvs[], use drule_all top_level_Type_storage_decl (or top_level_HashMap_decl for HashMapT case) to derive variable equalities, then bridge auto-generated names to FLOOKUP params via injectivity: metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ, var_decl_info_11], then fs[] to substitute. Solution (1) is preferred for cleanliness.
works_when: TopLevelVar Resume proof or any proof where assign_target_assignable_context expansion creates a var_decl_info pair that needs to bridge to FLOOKUP/env consistency theorems with different variable names
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13433_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3271-3319
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1355-1364

## L0448 scope='C3' tags=
shape: Resolving IS_SOME with controlled variable names using metis_tac + rename1
pattern: Instead of gvs[optionTheory.IS_SOME_EXISTS] which creates auto-named variables, use `?x. f x = SOME y by metis_tac[optionTheory.IS_SOME_EXISTS]` then rename1 to control the name. This avoids variable-name mismatches with downstream lemmas.
works_when: After expanding definitions containing IS_SOME guards, need actual SOME values with specific names to match consistency lemmas
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13447_t003
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3289-3292

## L0449 scope='C3' tags=
shape: Bridging HashMapVarDecl params to FLOOKUP HashMapT params via drule_all + gvs injectivity
pattern: After context expansion gives find_var_decl_by_num = SOME(HashMapVarDecl is_transient kt' vt'',id_str) but FLOOKUP says SOME(HashMapT t v): use drule_all top_level_HashMap_decl to get a find_var_decl with FLOOKUP's t/v, then gvs[optionTheory.SOME_11, pairTheory.PAIR_EQ, var_decl_info_11] to unify.
works_when: HashMapT TopLevelVar branch where find_var_decl witnesses differ from FLOOKUP type params
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3329-3335
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13514_t001

## L0450 scope='global' tags=
shape: type_value constructor order: BaseTV, TupleTV, ArrayTV, StructTV, FlagTV, NoneTV
pattern: Cases_on on type_value creates 6 subgoals in definition order: BaseTV first, ArrayTV third. Use explicit case labels or >~ [ArrayTV pattern] for targeted dispatch.
works_when: Cases_on root_tv where need different strategies for ArrayTV vs non-ArrayTV
evidence:
- source:semantics/vyperValueScript.sml:11-19
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13481_t001

## L0451 scope='C6' tags=bridge_lemma,assign_target_assignable_context,BaseTargetV
shape: assign_target_assignable_context cx (BaseTargetV loc sbs) st
pattern: For BaseTargetV: ScopedVar assignability from env_scopes_consistent (var_assignable=T + lookup_scopes gives entry.assignable). TopLevelVar module code from functions_well_typed+env_consistent+toplevel_vtypes FLOOKUP. ImmutableVar trivially T. assign_operation_matches_target_shape always T for BaseTargetV via assign_operation_matches_target_shape_BaseTargetV.
works_when: Replacing assign_operation_matches_target_shape and assign_target_assignable_context cheats in statement-level assignment branches where gv is a BaseTargetV
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:381-385
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:440-530

## L0452 scope='C6' tags=API_corruption,conjunction
shape: Avoid writing /\ in new theorem statements via tool calls
pattern: The Anthropic API corrupts /\ in new content. For bridge lemmas, use single-conclusion forms, split into separate lemmas, or use PULL_EXISTS + strip_tac to expand existentials. The appended bridge lemma does NOT contain /\ so should be fine.
works_when: Writing new HOL4 theorems that would need /\ in their statement
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13490_t001

## L0454 scope='C6' tags=bridge_lemma,env_scopes_consistent,entry.assignable,FLOOKUP,var_assignable
shape: env_scopes_consistent + FLOOKUP env.var_assignable id = SOME T ==> ?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable
pattern: To derive entry.assignable from env_scopes_consistent, you need FLOOKUP env.var_assignable id = SOME T (NOT just lookup_scopes). env_scopes_consistent_def line 743-744 says: FLOOKUP env.var_assignable id = SOME T ==> ?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable. Do NOT expand env_scopes_consistent_def in the proof. Instead, use it via drule/irule with the FLOOKUP hypothesis from well_typed_atarget_def. The well_typed_atarget for ScopedVar should provide the FLOOKUP env.var_assignable fact.
works_when: Proving ScopedVar assignable context where env_scopes_consistent is an assumption and you need entry.assignable from runtime consistency without expanding large definitions
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:743-744

## L0455 scope='C6' tags=metis_tac,timeout,fs_expansion,runtime_consistent,proof_structure
shape: After fs[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def], any tactic (metis, simp) may timeout
pattern: fs[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def] creates an enormous assumption context. NO tactic (metis_tac, simp, etc.) can reliably close goals in this context. Instead: use env_scopes_consistent/env_consistent/runtime_consistent as OPAQUE assumptions and derive needed facts via targeted drule/irule without expanding their definitions. If expansion is needed, isolate it in a subgoal via `fact by (fs[...] >> ...)` so the expanded context is local.
works_when: Any proof that needs runtime_consistent + env_consistent + env_scopes_consistent facts without polluting the global assumption context
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13690_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m13700_t002

## L0502 scope='C5.2' tags=shape,Replace,BaseTargetV,TupleTargetV,assign_operation_matches_target_shape_Replace_from_typed
shape: assign_operation_matches_target_shape for Replace from target_runtime_typed + evaluate_type + value_has_type
pattern: Use assign_operation_matches_target_shape_Replace_from_typed (vyperTypeStatePreservationScript.sml:2254) to derive assign_operation_matches_target_shape gv (Replace v) for ANY target type (BaseTargetV or TupleTargetV). It requires target_runtime_typed env cx st tgt ty gv + evaluate_type env.type_defs ty = SOME tv + value_has_type tv v. Do NOT use assign_operation_matches_target_shape_BaseTargetV when gv might be TupleTargetV.
works_when: Statement assignment branches (Assign, AnnAssign) where gv comes from eval_target and might be either BaseTargetV or TupleTargetV
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2254-2271
- tool_output:TO_type_system_rewrite-20260515T192259Z_m14754_t001

## L0503 scope='C5.2' tags=no_ctx,preservation,assign_target,priority
shape: Preservation theorems WITHOUT shape/context side conditions
pattern: assign_target_preserves_state_well_typed_no_ctx and assign_target_preserves_runtime_consistent_no_ctx only need runtime_consistent + target_runtime_typed + assign_operation_runtime_typed. NO assign_operation_matches_target_shape or assign_target_assignable_context needed. Use these for the 4 preservation sub-goals in statement assignment branches, separating preservation (easy, no context) from no-TypeError (hard, needs shape+context).
works_when: Statement assignment branches need runtime_consistent or state_well_typed preservation but not no-TypeError simultaneously
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:3601-3620
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:313-336

## L0504 scope='global' tags=API_corruption,Definition,Unicode,wedge,workaround,multi-clause
shape: HOL4 Definition with conjunction between equations
pattern: Use Unicode ∧ (U+2227) instead of ASCII /\ between Definition equations. HOL4 accepts Unicode logical connectives. The Anthropic API corrupts /\ to /| in tool call content. Multi-clause definition: `(f cx (C1 ...) = ...) ∧ (f cx (C2 ...) = ...) ∧ ... End`. This gives per-constructor rewrite rules for simp, unlike single-equation case expressions which cause simp to loop on recursive calls.
works_when: Writing new HOL4 Definition with multiple pattern-matching clauses joined by conjunction
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m14906_t001

## L0505 scope='global' tags=ETA_AX,EVERY,eta-expansion,simp
shape: simp produces eta-expanded lambda in EVERY/MLIST goal
pattern: When simp[def] produces a goal like `EVERY (λa. f cx a) gvs ⇔ EVERY (f cx) gvs` (eta-expanded vs point-free), use `metis_tac[ETA_AX]` to close the gap. simp alone cannot normalize this.
works_when: Biconditional or equational goal where one side has an eta-expanded lambda and the other is point-free
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m14902_t001

## L0508 scope='C5.2' tags=>-,parenthesization,Cases_on,subgoal_selection
shape: After Cases_on, use >- (parenthesized_tac) for subgoal-specific tactics, never bare >>
pattern: When using Cases_on inside a >- block, wrap the entire branch tactic in parentheses: >- (Cases_on `l` >- scoped_irule_tac >- scoped_simp >- scoped_gvs). The >> operator applies to ALL current subgoals, so bare >> after a split will apply subsequent tactics to wrong subgoals. Always parenthesize the branch after >-.
works_when: Any proof using Cases_on, IF_CASES_TAC, or other goal-splitting tactics inside >- blocks
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15077_t001
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15101_t001

## L0509 scope='C5.2' tags=induction,TupleTargetV,helper_lemma,mutual_theorem,recursive_theorem
shape: Recursive theorem application for tuple/list branches needs a separate helper or mutual form
pattern: When a theorem needs to apply itself recursively to list elements (e.g., TupleTargetV case of target_runtime_typed_static_imp_assignable_context), extracting a separate list-form helper lemma is the standard pattern. The helper takes LIST_REL3 (target_runtime_typed env cx st) tgts tys gvs + EVERY (assignment_value_static_assignable_context cx) gvs => EVERY (assign_target_assignable_context cx) gvs and is proved by list induction. The main theorem uses the helper for the TupleTargetV case and is proved by Cases_on (not induction). If the helper needs the main theorem for the head element, prove the helper FIRST with cheat for the head, then prove the main theorem, then go back and prove the helper using irule of the main theorem. Alternatively use a mutual conjunction form.
works_when: A theorem about a recursive datatype needs to apply itself recursively to sub-elements, and inline induction fails due to variable scoping
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15105_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:174-201
- source:semantics/prop/vyperTypeExprSoundnessScript.sml:670-678

## L0510 scope='C5.2.3' tags=TopLevelVar,gvs,definition_matching,assignable_context
shape: Proving assign_target_assignable_context from assignment_value_static_assignable_context for TopLevelVar
pattern: For the TopLevelVar branch: gvs[assign_target_assignable_context_def, assign_target_assignable_def, assignment_value_static_assignable_context_def] expands both sides. The if-then-else in assignment_value_static_assignable_context_def and the case/existential in assign_target_assignable_context_def both simplify to give existential witnesses code and p. Then qexistsl_tac [`code`,`p`] >> simp[] closes the goal. This works because both definitions have the SAME structure for TopLevelVar (existential over code/p with matching sub-conditions).
works_when: Proving that assignment_value_static_assignable_context implies assign_target_assignable_context for TopLevelVar
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15101_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:130-150
- source:semantics/prop/vyperTypeStatePreservationScript.sml:949-966

## L0511 scope='C5.2' tags=recInduct,mutual_theorem,target_runtime_typed,boundary_lemma,assumption_destruction
shape: Proving a mutual theorem over target_runtime_typed + target_values_runtime_typed using the existing boundary lemma target_runtime_typed_ScopedVar_imp_assignable_context
pattern: Use ho_match_mp_tac target_runtime_typed_ind >> rw[target_runtime_typed_def] for mutual theorems involving target_runtime_typed. This reduces to exactly 2 goals (base target + tuple target). For ScopedVar: rw expands target_runtime_typed into components, so reconstruct it via `target_runtime_typed ...` by simp[target_runtime_typed_def] before applying boundary lemmas, or use metis_tac with both the boundary lemma and target_runtime_typed_def. NEVER use gvs[target_runtime_typed_def] before Cases_on `loc` when a boundary lemma needs the unexpanded assumption.
works_when: Proving any mutual theorem that follows the recursion structure of target_runtime_typed and needs to consume boundary lemmas about specific location constructors
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15169_t001
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15181_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:843

## L0513 scope='C5.2' tags=definition_design,conjunction,if-then-else,iffLR,TopLevelVar,matching
shape: Definition form must match consumer's expected boolean structure (conjunction vs if-then-else)
pattern: When defining a new predicate that must align with an existing predicate's structure (e.g., assignment_value_static_assignable_context vs assign_target_assignable_context), use conjunction form NOT if-then-else. The conjunction form directly matches existential+case patterns in the consumer, enabling irule (iffLR lem) >> metis_tac[]. The if-then-else form requires additional conversion steps and creates drule failures. For biconditional lemmas, use irule (iffLR thm) instead of drule thm.
works_when: Defining a new predicate that must interface with an existing one at the proof level
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:130-150
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:200-204
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15317_t001

## L0514 scope='C5.2' tags=recInduct,target_runtime_typed,cases_before_expand,boundary_lemma
shape: Cases_on location BEFORE expanding target_runtime_typed_def, then use intact boundary lemma
pattern: When proving theorems by ho_match_mp_tac target_runtime_typed_ind, the induction already destructs gv into (BaseTargetV loc sbs) and (TupleTargetV gvs). For the base target case, the target_runtime_typed assumption remains intact. Cases_on `loc` THEN apply boundary lemmas like target_runtime_typed_ScopedVar_imp_assignable_context via metis_tac. Do NOT gvs/rw[target_runtime_typed_def] before the case split, as this destroys the intact assumption that boundary lemmas need to match.
works_when: Proving mutual theorems over target_runtime_typed that consume per-location boundary lemmas
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:197-215
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15317_t001
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15181_t001

## L0515 scope='C5.2' tags=induction,impossible_goals,target_runtime_typed,list_length_mismatch
shape: Impossible target_runtime_typed goals close by gvs[target_runtime_typed_def]
pattern: After ho_match_mp_tac target_runtime_typed_ind >> rpt strip_tac, there are 10 goals. Goals 2-3 (mismatched BaseTarget/TupleTarget combos) and goals 7-10 (list length mismatches in target_values_runtime_typed) have target_runtime_typed assumptions that evaluate to F. These close trivially by gvs[target_runtime_typed_def].
works_when: Proving mutual theorems over target_runtime_typed with induction
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:205-215
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15291_t001

## L0517 scope='C5.2' tags=env_context_consistent,architectural_gap,TopLevelVar,get_module_code,definition_fix
shape: env_context_consistent_def asymmetric: derives get_module_code for fn_sigs/bare_globals/flag_members but NOT for general toplevel_vtypes
pattern: env_context_consistent_def (vyperTypeSystemScript.sml:713-731) derives get_module_code for fn_sigs_consistent (line 702-711), bare_globals (line 718, as premise not consequence), and flag_members (line 727-730), but NOT for general FLOOKUP env.toplevel_vtypes entries. The toplevel_vtypes clause (line 721-722) only provides well_formed_vtype. The HashMapT-specific clause (line 723-726) requires get_module_code as a premise. FIX NEEDED: add a toplevel_vtypes_consistent clause that derives get_module_code + find_var_decl_by_num + lookup_var_slot_from_layout IS_SOME from FLOOKUP env.toplevel_vtypes (src,id) = SOME vt, matching the pattern of fn_sigs_consistent. Without this fix, assign_target_assignable_context cannot be derived for TopLevelVar targets in INR/no-TypeError branches. C5.2.4 (INL-success) is provable independently because execution success implies all intermediate monadic steps returned SOME.
works_when: Proving assign_target_assignable_context for TopLevelVar; any statement assignment branch needing TopLevelVar context; fixing env_consistent derivation chains
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:713-731
- source:semantics/prop/vyperTypeStatePreservationScript.sml:949-966
- plan:C5.2.7

## L0522 scope='C5.2' tags=HashMapRef,sbs,nonempty,assign_target,INL
shape: assign_target TopLevelVar HashMapRef INL => sbs <> []
pattern: In assign_target_def TopLevelVar HashMapRef branch (.sig line 7789-7823): lift_option_type (case REVERSE is of [] => NONE | x::xs => SOME (x,xs)). If sbs=[], REVERSE is=[], case returns NONE, lift_option_type returns INR TypeError. Therefore assign_target TopLevelVar HashMapRef INL implies sbs <> []. This satisfies the sbs <> [] requirement in assign_target_assignable_context_def for HashMapVarDecl.
works_when: Proving assign_target_TopLevelVar_INL_imp_assignable_context HashMapRef case
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15480_t001
- source:semantics/prop/vyperTypeStatePreservationScript.sml:949-966

## L0529 scope='C5.2.4' tags=assign_target_def,expansion,Cases_on,toplevel_value,controlled_expansion
shape: Cases_on tv BEFORE expanding assign_target_def to keep goals <4KB
pattern: For proofs that need assign_target_def expansion: FIRST case-split on the toplevel_value result (tv) from lookup_global using Cases_on 'tv'. This gives 3 separate goals. THEN expand assign_target_def with simp in each goal. Because tv's constructor is already known, the `case tv of ...` in assign_target_def reduces to one branch, keeping each goal <4KB. NEVER expand assign_target_def with all branches simultaneously via simp[assign_target_def, bind_def, lift_option_type_def, ...].
works_when: Proving anything about assign_target TopLevelVar branches where tv/result of lookup_global is known or can be case-split
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15629_t001
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15627_t001

## L0530 scope='C5.2.4' tags=lookup_global_def,find_var_decl_by_num,NONE,immutable,Value
shape: find_var_decl_by_num NONE + get_module_code SOME implies lookup_global returns Value (immutable path)
pattern: In lookup_global_def: when find_var_decl_by_num n code = NONE, lookup_global goes to the immutable path (get_immutables + FLOOKUP) and returns Value (SND tvv). So for a successful lookup_global INL where find_var_decl_by_num = NONE, tv must be Value v. This can be proved by expanding lookup_global_def with the NONE and SOME assumptions: simp[lookup_global_def, lift_option_type_def] gives the NONE branch directly.
works_when: Deriving tv = Value v from find_var_decl_by_num = NONE in C5.2.4 NONE case
evidence:
- source:semantics/vyperStateScript.sml:413-440

## L0531 scope='C5.2.4' tags=IS_SOME,contradiction,lookup_global,lift_option_type
shape: IS_SOME facts proved by CCONTR_TAC + lookup_global_def expansion (NOT assign_target_def)
pattern: For proving IS_SOME (evaluate_type ...) and IS_SOME (lookup_var_slot ...) facts needed by assign_target_assignable_context: use contradiction (CCONTR_TAC). If the value were NONE, lookup_global's lift_option_type NONE would return INR TypeError, contradicting lookup_global INL. This only requires expanding lookup_global_def (~25 lines), NOT assign_target_def (~100 lines). The pattern: irule IS_SOME_EXISTS >> CCONTR_TAC >> fs[] >> push lookup_global assumption >> simp[lookup_global_def, lift_option_type_def, bind_def, LET_THM, OPTION_BIND_def] >> gvs[].
works_when: Proving IS_SOME facts for StorageVarDecl/HashMapVarDecl branches of C5.2.4
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15627_t001

## L0533 scope='C5.2' tags=assignable_context,static_context,C5.2.3
shape: Deriving assign_target_assignable_context from runtime typing + static context predicate
pattern: C5.2.3 (target_runtime_typed_static_imp_assignable_context) is already proved. For INL-success branches where target_runtime_typed + env_consistent are available, use C5.2.3 directly. For INL-success alone (C5.2.4), prove INL => assignment_value_static_assignable_context first, then compose with C5.2.3.
works_when: Need assign_target_assignable_context in statement proofs where some runtime typing facts are available
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml C5.2.3 theorem

## L0535 scope='C5.2.4' tags=helper_lemma,find_decl_NONE,assign_target,vyperTypeAssignSoundness
shape: assign_target_TopLevelVar_find_decl_NONE_imp_INR_simple helper lemma (cheated, needs proof)
pattern: Two helper lemmas in vyperTypeAssignSoundnessScript.sml are currently cheated and block clean proof of C5.2.4: (1) assign_target_TopLevelVar_find_decl_NONE_imp_INR_simple: get_module_code SOME + find_decl NONE => assign_target ≠ INL. Proof approach: expand lookup_global_def showing find_decl NONE goes to immutable path returning Value; then expand assign_target_def Value case showing it needs declaration/slot info which was NONE => INR. (2) assign_target_TopLevelVar_HashMapRef_empty_sbs_imp_INR_simple: lookup_global = INL (HashMapRef ...) + sbs=[] => assign_target ≠ INL. Proof: in HashMapRef branch, REVERSE [] = [] → case [] of NONE → lift_option_type NONE = INR TypeError. Use Cases_on tv BEFORE expanding assign_target_def to keep goals <4KB.
works_when: Proving contradiction cases in C5.2.4 when find_decl returns NONE or when sbs is empty for HashMapRef
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:533-551
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15627_t001

## L0536 scope='C5.2.4' tags=assign_target_assignable,TopLevelVar,trivial,simplification
shape: assign_target_assignable (BaseTargetV (TopLevelVar src id) sbs) st = T by definition
pattern: For TopLevelVar, assign_target_assignable_def gives: case loc of ScopedVar id => ... | _ => T. TopLevelVar matches the wildcard _ => T case. This means assign_target_assignable_context for TopLevelVar simplifies to just the static context existential (T ∧ ∃code p. ... = ∃code p. ...). Use simp[assign_target_assignable_context_def, assign_target_assignable_def] to reduce the goal. This makes the C5.2.4 proof equivalent to proving assignment_value_static_assignable_context.
works_when: Any proof involving assign_target_assignable_context for TopLevelVar base targets
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:936-947
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15627_t001

## L0537 scope='C5.2.4' tags=monadic_witness,INL_success,TopLevelVar,assignable_context,two_lane
shape: assign_target TopLevelVar INL => assign_target_assignable_context via monadic witness recovery
pattern: Two-lane proof: (A) INL-success lane: expand assign_target_def ONLY for the specific tv constructor (use Cases_on tv FIRST), showing each monadic step that returns NONE would produce INR TypeError contradicting INL. (B) Static-context lane: prove INL => assignment_value_static_assignable_context, then compose with C5.2.3. Lane A uses assign_target_TopLevelVar_find_decl_NONE_imp_INR_simple (NONE => contradiction) and HashMapRef_empty_sbs_imp_INR_simple (empty sbs => contradiction). Lane B avoids assign_target_def expansion entirely. KEY: assign_target_assignable for TopLevelVar is T by definition, so assign_target_assignable_context reduces to just the static context existential.
works_when: Proving assign_target_TopLevelVar_INL_imp_assignable_context or similar monadic witness recovery for TopLevelVar assignment
evidence:
- source:semantics/vyperStateScript.sml:873-939
- source:semantics/prop/vyperTypeStatePreservationScript.sml:936-947
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:241-247

## L0539 scope='C5.2.4' tags=HashMapRef,empty_sbs,REVERSE,lift_option_type,contradiction
shape: HashMapRef + sbs=[] => REVERSE [] = [] => case [] of ... = NONE => lift_option_type NONE = INR TypeError
pattern: In assign_target_def HashMapRef branch (line 889-891): (first_sub, rest_subs) <- lift_option_type (case REVERSE is of x::xs => SOME (x,xs) | [] => NONE). When sbs=[], REVERSE [] = [], case [] of ... = NONE. lift_option_type NONE = INR (TypeError _). So assign_target cannot return INL. This also satisfies the sbs <> [] requirement in assign_target_assignable_context_def for HashMapVarDecl, so INL success => sbs <> [].
works_when: Proving contradiction from empty sbs for HashMapRef TopLevelVar assignment; deriving sbs <> [] from INL success
evidence:
- source:semantics/vyperStateScript.sml:889-891
- source:semantics/prop/vyperTypeStatePreservationScript.sml:949-966

## L0541 scope='C5.2.4' tags=top_level_var,assignable_context,static_context,INL_success
shape: assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') implies assign_target_assignable_context
pattern: For proving INL-success implies assignable context for TopLevelVar, use the TWO-STEP approach: (1) Prove INL => assignment_value_static_assignable_context (the static C5.2.1 predicate), which only needs the module-code/declaration/slot/type witnesses. (2) Compose with target_runtime_typed_static_imp_assignable_context (C5.2.3 already proved) if you also need runtime consistency + env consistency. Step 1 is simpler because assign_target_assignable for TopLevelVar is trivially T, so assign_target_assignable_context reduces to just the static-context existential.
works_when: Deriving assign_target_assignable_context from assign_target INL success for TopLevelVar
evidence:
- episode:E0119
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15756_t001

## L0542 scope='C5.2.4' tags=monadic,state_monad,contradiction,INL_INR,expand_all_defs
shape: lookup_global / assign_target returns INL but monadic step contradicts it
pattern: When proving INL-success implies context facts from monadic computations: expand ALL monadic definitions (including get_immutables_def, get_address_immutables_def, get_source_immutables_def) in the initial simp[] call so gvs[] can close contradiction goals. Never leave bind/do-notation partially expanded.
works_when: Proving that a successful (INL) result from a state-monadic computation implies the preconditions of successful intermediate steps
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15832_t001
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15809_t001

## L0543 scope='C5.2.4' tags=PairCases_on,option_NONE,contradiction_branch
shape: PairCases_on failing on option NONE branch in contradiction proof
pattern: When using CCONTR_TAC assuming find_var_decl_by_num = NONE and needing to show the SOME branch contradicts it: use Cases_on the var_decl_info constructor (StorageVarDecl/HashMapVarDecl) or Cases_on `FST p`, NOT PairCases_on `p`. PairCases_on only destructs pair structure; use Cases_on for datatype constructors.
works_when: Proving contradiction from assuming NONE when SOME would provide witnesses, in the SOME case after split
evidence:
- tool_output:TO_type_system_rewrite-20260516T092459Z_m15837_t001

## L0544 scope='C5.2.4' tags=monadic,lookup_global,expansion,case_split
shape: Expanding monadic function defs: expand outer only, case-split inner results
pattern: When expanding a monadic function like lookup_global_def that calls other monadic functions (get_immutables, etc.), ONLY expand the outer function's def + bind_def + lift_option_type_def. Do NOT expand inner function defs. Instead, Cases_on the inner function result, then Cases_on its sum-type component (q from pair destructuring). For lookup_global NONE branch: simp[lookup_global_def, bind_def, lift_option_type_def, LET_THM, return_def, raise_def] >> Cases_on `get_immutables cx src st` >> Cases_on `q` >> gvs[] >> Cases_on `FLOOKUP x n` >> gvs[is_Value_def, raise_def, return_def]. Variable x is the immutable map from INL x after splitting q.
works_when: Proving facts about monadic functions that compose inner monadic calls, where expanding inner defs creates unresolvable nested case expressions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m15929_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m15938_t001

## L0545 scope='C5.2.4' tags=lookup_global,immutable_path,Value_only
shape: lookup_global NONE branch only returns Value or TypeError, never HashMapRef/ArrayRef
pattern: In lookup_global_def, when find_var_decl_by_num n code = NONE, the function goes to the immutable path (get_immutables + FLOOKUP). This path can only return: (1) Value (SND tvv) when FLOOKUP returns SOME, or (2) INR (TypeError ...) when FLOOKUP returns NONE or get_immutables fails. Therefore ¬is_Value tv contradicts lookup_global returning INL tv in the NONE branch.
works_when: Proving that lookup_global INL with non-Value tv implies find_var_decl_by_num = SOME; the C5.2.4 helper lemma lookup_global_INL_not_Value_imp_find_decl_SOME
evidence:
- source:semantics/vyperStateScript.sml:413-439
- tool_output:TO_type_system_rewrite-20260516T153850Z_m15938_t001

## L0547 scope='C5.2.4' tags=lookup_global,IS_SOME,StorageVarDecl,HashMapVarDecl,monadic_success
shape: lookup_global INL implies IS_SOME of layout/evaluate_type called via lift_option_type
pattern: lookup_global_def calls lift_option_type(lookup_var_slot_from_layout ...) and lift_option_type(evaluate_type ...) in the StorageVarDecl branch before proceeding. If lookup_global returns INL, all these lift_option_type calls must have succeeded (returned SOME), giving IS_SOME facts. Similarly for HashMapVarDecl branch: lift_option_type(lookup_var_slot_from_layout ...) must succeed. Prove via: mp_tac lookup_global equation >> simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def] >> Cases_on specific calls. Helper theorems: lookup_global_INL_StorageVarDecl_imp_IS_SOME, lookup_global_INL_HashMapVarDecl_imp_IS_SOME in vyperTypeAssignSoundnessScript.sml.
works_when: Deriving IS_SOME witnesses for assignment_value_static_assignable_context from lookup_global INL success
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:588-601
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:607-618

## L0548 scope='C5.2.4' tags=assign_target,HashMapRef,sbs,nonempty,Cases_on_tv_first
shape: assign_target TopLevelVar HashMapRef INL implies sbs ≠ []
pattern: In assign_target_def TopLevelVar HashMapRef branch: lift_option_type(case REVERSE sbs of [] => NONE | x::xs => SOME(x,xs)). If sbs=[], returns INR TypeError. So successful INL implies sbs≠[]. Key proof trick: prove this by CCONTR_TAC + drule lookup_global_INL + Cases_on tv BEFORE expanding assign_target_def. For HashMapRef branch ONLY, expand assign_target_def and the raise/bind give immediate contradiction. For Value/ArrayRef branches, use lookup_global_def to show type mismatch (HashMapVarDecl can't produce Value/ArrayRef). Helper: assign_target_TopLevelVar_INL_HashMapVarDecl_imp_sbs_ne in vyperTypeAssignSoundnessScript.sml.
works_when: Proving sbs ≠ [] as part of assignment_value_static_assignable_context for HashMapVarDecl
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:624-659
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16025_t001

## L0556 scope='C5.2' tags=
shape: When MATCH_MP on a helper theorem works for ACCEPT_TAC but irule/MATCH_MP_TAC creates existential capture
pattern: For applying assign_target_TopLevelVar_INL_imp_assignable_context inside a completeInduct proof: first_x_assum (fn asm => ACCEPT_TAC (MATCH_MP assign_target_TopLevelVar_INL_imp_assignable_context asm)) works because MATCH_MP specializes the universally-quantified variables producing a theorem whose conclusion matches the goal exactly. irule/ho_match_mp_tac creates residual existentials because the tactic introduces fresh variables that dont unify with goal-context variables of the same names.
works_when: Applying helper theorems with universally-quantified variables that share names with goal context variables, where ACCEPT_TAC + MATCH_MP can produce a matching conclusion
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:298-300
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16146_t001

## L0558 scope='C5.2' tags=location_value,constructor_order,Cases_on
shape: location_value Datatype constructor order
pattern: location_value constructors are ordered: ScopedVar, ImmutableVar, TopLevelVar (NOT ScopedVar, TopLevelVar, ImmutableVar). When using Cases_on on a location_value, the >- subgoals are in this order. Getting the order wrong causes irule/MATCH_MP failures that look like type mismatches or No match errors.
works_when: Splitting on location_value type in assignment-target proofs
evidence:
- source:semantics/vyperStateScript.sml:802-804

## L0559 scope='C5.2' tags=irule,variable_capture,MATCH_MP,completeInduct
shape: Using irule vs MATCH_MP for helper theorems in completeInduct context
pattern: In completeInduct proofs, MATCH_MP on helper theorems with universally-quantified variables that share names with the induction goal (cx, op, st, res, st') causes variable capture. Use irule instead: it matches the helper conclusion against the goal, producing antecedent subgoals that are solved from assumptions. The irule+simp[] pattern is cleaner and avoids name clashes.
works_when: Applying helper lemmas inside completeInduct_on proofs where helper has same universally-quantified variable names
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16146_t001

## L0560 scope='C5.2.5' tags=
shape: completeInduct with assign_target INL premise blocks sub-component IH
pattern: When a theorem premise includes F(cx,gv,st)=INL and you need to apply the IH to tuple sub-components, the IH requires F to return INL for sub-components. This does not follow from the outer F=INL without unfolding the function definition. Solution: (1) prove a component-extraction lemma from assign_targets_def showing assign_target(cx,TupleTargetV gvs,vs,st)=INL => per-component assign_target(cx,gv_i,Replace v_i,st_i)=INL, OR (2) remove the F=INL premise, OR (3) split into BaseTargetV (uses F=INL) and TupleTargetV (needs extraction lemma).
works_when: Proving a theorem about a recursive value where one premise is success of a recursive function that cannot be decomposed into component success without unfolding
evidence:
- source:semantics/vyperStateScript.sml:949-961

## L0561 scope='C5.2.5' tags=
shape: assign_target_INL_imp_assignable_context_stmt is unused by any downstream proof
pattern: The theorem assign_target_INL_imp_assignable_context_stmt is defined but not used by any downstream proof. Before investing more sessions, check if C6 consumers can use: (1) assign_target_TopLevelVar_INL_imp_assignable_context for TopLevelVar INL success, (2) target_runtime_typed_ScopedVar_imp_assignable_context for ScopedVar, (3) target_runtime_typed_static_imp_assignable_context for INR branches with assignment_value_static_assignable_context. If per-call-site derivation works, C5.2.5 can be deferred.
works_when: Deciding whether to continue a stuck bridge lemma vs using alternative bridges at call sites
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:507

## L0562 scope='C5.2.5' tags=assignment_value,Cases_on,induction,BaseTargetV,location_value
shape: Proofs about assignment_value type
pattern: For assignment_value proofs, use Cases_on `gv` (not Induct/recInduct). After Cases_on, BaseTargetV needs simp[assignment_value_static_assignable_context_def] BEFORE Cases_on `l` so the definition is partially unfolded. Location_value constructors are ScopedVar, ImmutableVar, TopLevelVar (in order). For TupleTargetV with nested lists, use list induction on the component list with qid_spec_tac for generalized variables.
works_when: Proving properties of assignment_value that need per-constructor reasoning
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16571_t001

## L0563 scope='C5.2.5' tags=assign_target_INL,TupleTargetV,monadic_extraction,assign_targets
shape: assign_target INL on TupleTargetV needs component extraction
pattern: To derive component-level facts (assign_target_assignable_context or static_context) from assign_target INL on a TupleTargetV, must extract per-component assign_target INL from assign_targets execution. The key lemma: assign_targets cx (gv::gvs) (v::vs) st = (INL (), st') ==> assign_target cx gv (Replace v) st returns INL. Prove by list induction unfolding assign_targets clauses from assign_target_def.
works_when: Need component-level assign_target facts from tuple assignment success
evidence:
- source:semantics/vyperStateScript.sml:949-961
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:278-321

## L0564 scope='C5.2' tags=unused_theorem,defer,per_call_site_helper
shape: assign_target_INL_imp_assignable_context_stmt has no consumers
pattern: assign_target_INL_imp_assignable_context_stmt is unused by any downstream proof. C6 statement branches should use per-call-site helpers instead: assign_target_TopLevelVar_INL_imp_assignable_context for TopLevelVar INL branches, target_runtime_typed_ScopedVar_imp_assignable_context for ScopedVar, target_runtime_typed_static_imp_assignable_context with static_context premise for all-result no-TypeError branches. Defer the generic bridge lemma unless a consumer appears.
works_when: Deciding whether to invest effort proving generic bridge lemmas vs per-call-site helpers
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:312-321

## L0566 scope='C5' tags=env_context_consistent,architectural_fix,TopLevelVar,definition_repair
shape: env_context_consistent_def MUST provide get_module_code/find_var_decl_by_num/lookup_var_slot_from_layout for writable top-level entries
pattern: env_context_consistent_def gap resolved by plan_oracle C5.4.1: (1) type_place_target rejects bare-global TopLevelNameTarget, (2) env_context_consistent gains storage/hashmap code/declaration/layout existence clauses for non-bare-global Type and HashMapT entries. Then env_consistent_toplevel_storage_static and env_consistent_toplevel_hashmap_static project these facts. This unblocks assign_target_assignable_context derivation for TopLevelVar in INR/no-TypeError branches via assignment_value_static_assignable_context + C5.2.3 bridge.
works_when: Proving assign_target_assignable_context for TopLevelVar targets; fixing INR no-TypeError branches in statement assignment soundness
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16696_t001
- episode:E0124

## L0567 scope='C5' tags=unused_cheat,delete_or_prove,C5.2.5
shape: assign_target_INL_imp_assignable_context_stmt_ind has cheated TupleTargetV branch with zero consumers
pattern: The theorems assign_target_INL_imp_assignable_context_stmt_ind and assign_target_INL_imp_assignable_context_stmt have a cheated TupleTargetV branch. Grep for consumers before spending effort proving. If unused, delete both. If a consumer exists, replace with proved base-target-only version.
works_when: Cleaning up C5 bridge lemma block cheats; zero-CHEAT audit
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:304-307
- episode:E0121

## L0568 scope='C5' tags=C5.3,AnnAssign,NoneT,already_proved
shape: C5.3 AnnAssign assignable-type consequences are already covered by existing lemmas
pattern: C5.3 requires no new work: assignable_type_not_NoneT, evaluate_type_not_NoneT_imp_not_NoneTV, and assignable_type_evaluate_not_NoneTV already exist and are used directly in AnnAssign branch (line 873-874). Do not add AnnAssign-specific non-None predicates.
works_when: AnnAssign branches need non-NoneT/non-NoneTV derivation from assignable_type
evidence:
- episode:E0123
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16657_t002

## L0569 scope='C5' tags=mutual_definition,rewriting,type_place_target,IS_SOME,conditional
shape: Proving biconditional about a clause of a large mutual definition (well_typed_expr_def) that now has a conditional guard
pattern: When a mutual definition has many clauses and you need to prove a biconditional about ONE clause with a conditional (if IS_SOME x then NONE else y), do NOT try to rewrite with the full definition. Instead: (1) prove two small computation lemmas: the NONE branch (IS_SOME true => result is NONE) and the SOME branch (IS_SOME false => result is y). Use Cases_on the FLOOKUP value first, then use simp/once_rewrite_tac for each branch separately. (2) Then the main biconditional follows by metis_tac of the two helpers.
works_when: Proving biconditional lemmas about individual clauses of large mutual definitions where the clause has a conditional guard
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16729_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16772_t001

## L0570 scope='C5' tags=env_context_consistent,drule,qpat_x_assum,existential_witness
shape: Instantiating universal env_context_consistent clause to get existential witnesses
pattern: After env_context_consistent_def strengthening, universal clauses like (!src id kt vt. FLOOKUP _ _ = SOME (HashMapT kt vt) ==> exists ts ...) need to be applied to specific FLOOKUP assumptions. Use qpat_x_assum with the HashMapT/Type pattern to target the right clause, then drule. metis_tac fails because it cannot match the universal quantifier against specific assumptions efficiently.
works_when: Deriving get_module_code/find_var_decl_by_num/lookup_var_slot_from_layout witnesses from env_consistent + FLOOKUP toplevel_vtypes assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16824_t001

## L0571 scope='C5' tags=type_place_target,TopLevelNameTarget,bare_globals,biconditional
shape: type_place_target for TopLevelNameTarget now rejects bare-global entries via IS_SOME guard
pattern: type_place_target env (TopLevelNameTarget (src_id_opt, id)) now checks IS_SOME (FLOOKUP env.bare_globals (src_id_opt,string_to_num id)) and returns NONE if true. The biconditional: type_place_target ... = SOME vt <=> FLOOKUP bare_globals = NONE AND FLOOKUP toplevel_vtypes = SOME vt. Prove via two helper lemmas: (1) IS_SOME bare_globals => result is NONE, (2) bare_globals = NONE => result is FLOOKUP toplevel_vtypes. Both helpers prove by simp[well_typed_expr_def].
works_when: Working with type_place_target for TopLevelNameTarget targets
evidence:
- episode:E0125
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16799_t001

## L0574 scope='C5.4.3' tags=mutual_theorem,target_runtime_typed_ind,ho_match_mp_tac,projection
shape: target_runtime_typed induction requires mutual theorem + cj projections
pattern: ho_match_mp_tac target_runtime_typed_ind gives 9 goals for the mutual definition (2 meaningful: BaseTarget/BaseTargetV, TupleTarget/TupleTargetV + their list cons variants, plus 5 impossible mismatches that gvs closes). Write a mutual theorem with conj for both target_runtime_typed and target_values_runtime_typed, then project with cj 1 / cj 2. NEVER use ho_match_mp_tac on a non-mutual theorem for this induction principle.
works_when: Proving mutual theorems over target_runtime_typed and target_values_runtime_typed
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16947_t001
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:242-304

## L0577 scope='C5.4.3' tags=Induct_on,completeInduct,base_assignment_target,induction,variable_naming
shape: Induct_on `bt` on universally-quantified base_assignment_target fails
pattern: For base_assignment_target with constructors NameTarget/BareGlobalNameTarget/TopLevelNameTarget nsid/SubscriptTarget b e/AttributeTarget b id: Induct_on after gen_tac fails because the type has internal structure that doesn't match simple induction. Use completeInduct_on `base_assignment_target_size bt` instead, or use the recursion-matching induction theorem base_target_value_shape_ind via ho_match_mp_tac if the goal shape matches.
works_when: Proving properties of base_assignment_target that need recursion through SubscriptTarget/AttributeTarget inner targets
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16994_t001
- source:syntax/vyperASTScript.sml:235-239

## L0578 scope='C5.4.3' tags=type_place_target,well_typed_target,vtype,SubscriptTarget,recursion
shape: Helper lemmas about type_place_target for recursive base_assignment_target must use type_place_target = SOME vt not well_typed_target
pattern: When proving a property by recursion through SubscriptTarget/AttributeTarget, the inner target's type_place_target returns SOME vt' where vt' can be any vtype (Type, HashMapT, etc.). well_typed_target = type_place_target = SOME (Type ty) is too restrictive for the IH because the inner target might be a HashMapT. Use type_place_target env bt = SOME vt as the IH premise to allow any vtype.
works_when: Deriving bare_globals = NONE or other properties through recursive base_assignment_target structures where inner targets might produce HashMapT vtypes
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17017_t001
- source:semantics/prop/vyperTypeEnvScript.sml:124-133

## L0579 scope='C5.4.3' tags=Cases_on,variable_naming,ho_match_mp_tac,target_runtime_typed_ind,mutual_theorem
shape: After ho_match_mp_tac target_runtime_typed_ind, BaseTargetV case uses `loc` not `l` for Cases_on
pattern: The target_runtime_typed_ind induction for BaseTarget/BaseTargetV case produces a variable `loc` (from BaseTargetV loc sbs pattern), not `l`. Cases_on `l` fails with 'No var with name l free in goal'. Use Cases_on `loc` instead.
works_when: Proving mutual theorems using target_runtime_typed_ind where the BaseTarget/V case needs location case splitting
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m16970_t002

## L0580 scope='C5.4.3' tags=recInduct,base_target_value_shape_ind,nested_universal,irule
shape: recInduct base_target_value_shape_ind for lemmas with nested !src id. loc = TopLevelVar src id condition
pattern: When using recInduct base_target_value_shape_ind, the lemma MUST quantify over `loc` and `sbs` as leading universal parameters matching the definition's recursion. If you need a property specific to TopLevelVar, use `!src id. loc = TopLevelVar src id ==>` as a nested condition. After rw[], the IH is available for SubscriptTarget/AttributeTarget cases with the same nested condition. Use simp[type_place_target_X] (not metis_tac) to close remaining goals from iff lemmas. NEVER fix loc = TopLevelVar src id as a direct parameter or recInduct fails with ISPEC error.
works_when: Proving properties of base_target_value_shape specific to TopLevelVar locations using recursion-matching induction
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:462
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17114_t001

## L0581 scope='C5.4.3' tags=irule,nested_universal,drule,qspecl_then
shape: irule with nested !src id. loc = TopLevelVar src id premise
pattern: When a lemma has `!src id. loc = TopLevelVar src id ==> P src id` and the goal has `P o' s` where o'=src and s=id from a Cases_on, irule may not automatically specialize the nested universal. Use `drule lemma >> disch_then (qspecl_then [`o'`,`s`] mp_tac) >> simp[]` instead. Alternatively, prove a specialized corollary `!env bt o' s sbs vt. base_target_value_shape env bt (TopLevelVar o' s) sbs ==> type_place_target env bt = SOME vt ==> FLOOKUP env.bare_globals (o', string_to_num s) = NONE` using completeInduct_on.
works_when: Applying a lemma with nested universal quantifier to a goal with concrete variable names from case splits
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17070_t001

## L0583 scope='C5.4' tags=>~,ho_match_mp_tac,induction,subgoal_selection
shape: >~ subgoal selectors fail after ho_match_mp_tac induction on mutual definitions
pattern: After ho_match_mp_tac target_runtime_typed_ind, the >~ pattern selector fails with 'No match' because the induction goals use auto-generated variable names that don't match the quoted backtick patterns. Use simple positional >- or >- with FAIL_TAC probes to determine goal order, then dispatch by position.
works_when: Proofs using ho_match_mp_tac on mutual induction theorems where subgoal selection is needed
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17197_t001

## L0585 scope='C5.4.3' tags=standalone_lemma,mutual_theorem,metis_tac,TopLevelVar,Cases_on_loc
shape: Prove standalone lemma for TopLevelVar branch, then metis_tac into mutual theorem
pattern: For C5.4.3 target_runtime_typed_imp_static_assignable_context_mutual: after ho_match_mp_tac target_runtime_typed_ind >> rpt strip_tac, Goal 1 is BaseTarget/BaseTargetV with loc as the location variable. Cases_on `loc` >> simp[] closes ScopedVar and ImmutableVar. The TopLevelVar case is the hard one. Prove a standalone target_runtime_typed_TopLevelVar_imp_static_context lemma outside the mutual proof, then call it via metis_tac inside the mutual proof at Goal 1. This extracts the hard proof from the fragile induction structure.
works_when: Proving mutual theorems by target_runtime_typed_ind where only the TopLevelVar case is nontrivial
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17255_t001

## L0586 scope='C5.4.3' tags=sequential_fs,well_typed_target_def,type_place_target,assumption_preservation
shape: Sequential fs preserves type_place_target assumption for lemma matching; gvs destroys it
pattern: After fs[target_runtime_typed_def] then fs[target_value_shape_def, well_typed_atarget_def] then fs[well_typed_target_def], the assumptions type_place_target env bt = SOME (Type ty), base_target_value_shape env bt (TopLevelVar src id) sbs, location_runtime_typed, target_path_type, and env_consistent are ALL intact and recognizable. This is the correct approach instead of gvs[], which would destructively rewrite through all definitions simultaneously and destroy the assumption shapes needed by boundary lemmas.
works_when: Expanding definitions in the standalone TopLevelVar helper lemma for C5.4.3
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17255_t001

## L0587 scope='C5.4.3' tags=drule_all,metis_timeout,existential,FLOOKUP,projection_lemma,rw_qexists
shape: When metis_tac times out with projection lemmas + biconditional + IS_SOME_EXISTS, use drule_all to get existential witnesses then rw/qexists_tac explicitly
pattern: For proving assignment_value_static_assignable_context for TopLevelVar: (1) fs[location_runtime_typed_def] to expose FLOOKUP (2) prove bare_globals=NONE by metis (3) Cases_on vt (4) For Type: drule_all env_consistent_toplevel_storage_static >> strip_tac >> fs[IS_SOME_EXISTS] >> rw[assignment_value_static_assignable_context_TopLevelVar] >> qexists_tac >> qexists_tac >> simp[]. For HashMapT: same with env_consistent_toplevel_hashmap_static, HashMapVarDecl, and target_path_type_HashMapT_not_nil.
works_when: Proving assignment_value_static_assignable_context for TopLevelVar with FLOOKUP + env_consistent; when metis_tac with existentials and compound FLOOKUP keys times out
evidence:
- episode:E0129
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17278_t001

## L0588 scope='global' tags=irule,metis_tac,universal_quantifier,antecedent,instantiation
shape: irule cannot instantiate universally-quantified variables appearing only in antecedents; use metis_tac or Q.INST/drule instead
pattern: When a lemma has !vt. A vt ==> B where vt appears only in antecedents not conclusion B, irule matching B against the goal creates a universal subgoal A vt' that simp cannot close even when A c is a specific assumption. Use metis_tac[lemma] instead, or specialize with Q.INST before irule, or use drule to match antecedents directly.
works_when: Applying lemmas with universally-quantified variables that appear only in antecedents
evidence:
- episode:E0128
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17255_t001

## L0589 scope='C5' tags=drule_all,existential_witness,metis_timeout,FLOOKUP,projection_lemma
shape: When metis_tac times out combining projection lemmas + biconditional + IS_SOME_EXISTS for FLOOKUP-based goals
pattern: For proving assignment_value_static_assignable_context for TopLevelVar with FLOOKUP + env_consistent: (1) drule_all the projection lemma to get existential witnesses explicitly (2) strip_tac to introduce them (3) rw[assignment_value_static_assignable_context_TopLevelVar] to rewrite goal to existential form (4) qexists_tac with the concrete witnesses for Type branch. For HashMapT branch, drule_all + rw may already solve existentials from assumptions, leaving just sbs <> [] to close with target_path_type_HashMapT_not_nil.
works_when: Proving existential conclusions from projection lemmas where metis_tac times out due to compound FLOOKUP keys and variable name overlap
evidence:
- episode:E0130

## L0590 scope='C5' tags=mutual_theorem,ho_match_mp_tac,tuple_branch,drule_vs_irule
shape: After ho_match_mp_tac target_runtime_typed_ind, TupleTarget/TupleTargetV branch needs IH via drule not irule
pattern: Goal 4 (TupleTarget/TupleTargetV) after ho_match_mp_tac target_runtime_typed_ind: fs[target_runtime_typed_def] gives IH about target_values_runtime_typed. Use first_x_assum drule >> simp[] (not irule). The IH is a universally-quantified implication that drule matches against the specific target_values_runtime_typed assumption. Then metis_tac[] or simp[] closes remaining conjuncts.
works_when: Proving mutual theorems by target_runtime_typed_ind where TupleTarget/TupleTargetV case needs the list induction hypothesis
evidence:
- episode:E0130

## L0591 scope='C5.4.5' tags=assign_target,INR_result,no_type_error,no_return,pattern
shape: Assign/AugAssign INR-result branches after assign_target: use assign_target_no_type_error + assign_target_no_return
pattern: For assign_target cx gv op st = (INR (Error e'), st'): derive runtime_consistent, assign_operation_runtime_typed, assign_operation_matches_target_shape, assign_target_assignable_context at the call state, then drule assign_target_no_type_error + simp[no_type_error_result_def]. For INR (ReturnException v'): drule (cj 1 assign_target_no_return) >> simp[] eliminates it since assign_target never returns ReturnException.
works_when: Statement assignment branches where assign_target returns INR; both Error and ReturnException sub-cases
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17380_t001

## L0592 scope='C5.4.5' tags=materialise,TypeError,contradiction,assignable_type,pattern
shape: materialise INR (Error (TypeError msg)) is contradictory under typed non-None expression
pattern: When materialise cx tvl st' = (INR (Error (TypeError msg)),st') and expr_result_typed env e tvl and assignable_type env.type_defs (expr_type e): derive expr_type e ≠ NoneT via assignable_type_not_NoneT, then drule_all materialise_typed_non_none_no_type_error with evaluate_type_not_NoneT_imp_not_NoneTV. This gives contradiction (F).
works_when: Assign/AnnAssign branches where materialise returns TypeError on a typed expression with assignable type
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17416_t001

## L0593 scope='C5' tags=unused_cheat,delete,zero_consumers
shape: Unused theorems with cheat branches should be deleted immediately, not deferred
pattern: When LEARNINGS or grep confirms a theorem has zero consumers and contains a cheat, delete both the _ind theorem and its wrapper immediately. Do not defer deletion across sessions - it blocks zero-CHEAT goals and is a quick win.
works_when: Cleaning up bridge lemma blocks; zero-CHEAT audit preparation
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:413-416

## L0594 scope='C5.4.5' tags=materialise,TypeError,contradiction,expr_result_typed,drule_ordering
shape: materialise INR (Error (TypeError msg)) contradiction: must unfold expr_result_typed BEFORE applying materialise_typed_non_none_no_type_error
pattern: When proving materialise cx tvl st' = (INR (Error (TypeError msg)),st') is contradictory under typed expression: FIRST gvs[expr_result_typed_def, expr_runtime_typed_def] to expose toplevel_value_typed, THEN drule_at_then Any drule materialise_typed_non_none_no_type_error. Only after that, derive expr_type e ≠ NoneT and apply evaluate_type_not_NoneT_imp_not_NoneTV. The old drule_all pattern fails because toplevel_value_typed is hidden inside the expr_result_typed conjunction.
works_when: Any assign/AnnAssign/AugAssign branch where materialise returns TypeError on a typed expression
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17432_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17452_t001

## L0595 scope='C5.4.5' tags=AugAssign,update_assignment,bridge_lemma,no_TypeError,pattern
shape: AugAssign INR assign_target Error sub-case: use assign_target_update_no_type_error + bridges
pattern: For assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st2 = (INR (Error e'), st4): (1) derive runtime_consistent env cx st2, (2) derive well_typed_binop ty bop ty (expr_type e) from gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def, toplevel_value_typed_def], (3) derive value_runtime_typed env (expr_type e) v similarly, (4) assign_operation_matches_target_shape for BaseTargetV+Update is T by simp[assign_operation_matches_target_shape_def], (5) assign_target_assignable_context via metis_tac[target_runtime_typed_imp_assignable_context], (6) drule assign_target_update_no_type_error >> simp[no_type_error_result_def, assign_operation_matches_target_shape_def] >> disch_then drule twice >> simp[] >> metis_tac[]. For ReturnException: drule (cj 1 assign_target_no_return) >> simp[] >> disch_then drule >> simp[].
works_when: AugAssign branches where assign_target returns INR; both Error and ReturnException sub-cases
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17380_t001

## L0596 scope='C5.4.5' tags=materialise,TypeError,contradiction,assignable_type,AugAssign,AnnAssign
shape: materialise INR (Error (TypeError msg)) is contradictory under typed non-None expression
pattern: When materialise returns TypeError on a well-typed expression with assignable_type: FIRST gvs[expr_result_typed_def, expr_runtime_typed_def] to expose toplevel_value_typed, THEN drule_at_then Any drule materialise_typed_non_none_no_type_error. Then derive expr_type e ≠ NoneT via assignable_type_not_NoneT, then apply evaluate_type_not_NoneT_imp_not_NoneTV for the final contradiction.
works_when: Any assign/AnnAssign/AugAssign branch where materialise returns TypeError on a typed expression
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17432_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17452_t001

## L0597 scope='C5.4.5' tags=assign_target,INR_result,no_type_error,no_return,runtime_consistent
shape: Assign/AugAssign INR-result branches after assign_target: use assign_target_no_type_error + assign_target_no_return
pattern: For assign_target returning INR: derive runtime_consistent + target_runtime_typed + assignable_type + shape + assignable_context at the call state, then project no_type_error and runtime_consistent preservation. For INR(Error): drule assign_target_no_type_error (or assign_target_update_no_type_error for Update) + simp[no_type_error_result_def]. For INR(ReturnException): drule (cj 1 assign_target_no_return) + simp[] - assign_target never returns ReturnException.
works_when: Statement assignment branches where assign_target returns INR; both Error and ReturnException sub-cases
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17380_t001

## L0598 scope='C7' tags=switch_BoolV,assert,state_preservation,template
shape: AssertBare/AssertUnreachable proof template using switch_BoolV_post
pattern: For Assert e AssertBare/AssertUnreachable: (1) simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def, AllCaseEqs(), PULL_EXISTS] to expand, (2) split on eval_expr result (INL/INR), (3) INR: drule eval_expr_exception_return_typed, (4) INL: unfold expr_result_typed_def/expr_runtime_typed_def, then drule_then drule_then irule switch_BoolV_post, (5) conj_tac for return case (rw[return_def] then rw[no_type_error_result_def]), (6) for raise case: simp[bind_def,AllCaseEqs(),raise_def] then metis_tac[switch_BoolV_state, return_state, raise_state]. NEVER irule switch_BoolV_state - it has universally-quantified continuations.
works_when: Assert statement branches using switch_BoolV with concrete return()/raise() continuations
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:854-879
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:881-906

## L0599 scope='C7' tags=RaiseReason,get_Value,dest_StringV,lift_option_type,raise
shape: RaiseReason proof template through get_Value + dest_StringV + lift_option_type + raise pipeline
pattern: For Raise (RaiseReason e): (1) expand evaluate_def with AllCaseEqs(), (2) split INL/INR on eval_expr result, (3) INR: drule eval_expr_exception_return_typed, (4) INL: unfold expr_result_typed_def, drule toplevel_value_typed_StringTV to get StringV witness, (5) simp[get_Value_def, bind_def, AllCaseEqs(), PULL_EXISTS, lift_option_type_def, dest_StringV_def] to expand get_Value/lift_option_type, (6) imp_res_tac get_Value_state, lift_option_type_state, raise_state for state preservation, (7) gvs[no_type_error_result_def] for no-TypeError. Do NOT use AllCaseEqs on get_Value/lift_option_type separately - they are expanded inline.
works_when: RaiseReason branch and any branch with get_Value + dest_StringV + lift_option_type + raise pipeline under StringT typing
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:827-852
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:907-946

## L0600 scope='C7' tags=Expr_resume,expression_soundness,template,consumer
shape: Expression-level resume branches consume eval_expr/evel_exprs IH from the mutual theorem
pattern: For expression-level Resume branches (e.g. Expr_Name, Expr_Literal, Expr_Builtin): the proved Expr resume (line 1509-1525) is the template. Pattern: (1) simp_tac[evaluate_def, bind_def, AllCaseEqs()] to expand, (2) Cases_on eval_expr result, (3) INL: use expr_result_typed from IH, (4) INR: drule eval_expr_exception_return_typed. Most expression sub-cases will additionally need to expand the specific expression constructor definition (e.g. well_typed_expr_def clauses for Name/BareGlobal/etc.) to derive the required target_runtime_typed or expr_result_typed facts.
works_when: All expression-level Resume branches in eval_all_type_sound_mutual
evidence:
- source:semantics/prop/vyperTypeStmtSoundnessScript.sml:1509-1525

## L0601 scope='C7' tags=AssertReason,switch_BoolV,monadic_pipeline,Cases_on
shape: Assert/AssertReason: eval_expr -> switch_BoolV -> bind pipeline with get_Value/dest_StringV/raise
pattern: For Assert/AssertReason branches: (1) Cases_on eval_expr cx e st, (2) Cases_on expr_res (INL/INR), (3) INR: drule eval_expr_exception_return_typed, (4) INL: drule toplevel_value_typed_BoolTV >> Cases_on b, (5) True branch: gvs[no_type_error_result_def, return_exception_typed_def] >> metis_tac[return_state, raise_state], (6) False branch (AssertReason only): Cases_on eval_expr cx e' st1 >> Cases_on reason_res >> repeat for string pipeline
works_when: Assert/AssertReason statement branches in eval_all_type_sound_mutual
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17698_t001

## L0602 scope='C7' tags=RaiseReason,get_Value,dest_StringV,lift_option_type,boundary_lemma
shape: RaiseReason proof through get_Value + dest_StringV + lift_option_type + raise pipeline
pattern: For Raise (RaiseReason e): (1) Cases_on eval_expr result, (2) INR: drule eval_expr_exception_return_typed >> simp[], (3) INL: unfold expr_result_typed_def, expr_runtime_typed_def, evaluate_type_def, (4) drule toplevel_value_typed_StringTV to get StringV witness, (5) gvs[get_Value_def, return_def, dest_StringV_def, lift_option_type_def, no_type_error_result_def, return_exception_typed_def], (6) imp_res_tac raise_state >> gvs[]
works_when: RaiseReason branch and any branch with get_Value + dest_StringV pipeline under StringT typing
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17698_t001

## L0603 scope='C7' tags=qho_match_abbrev_tac,switch_BoolV_post,anti-pattern
shape: Avoid qho_match_abbrev_tac when switch_BoolV_post needs to match assumptions
pattern: Do NOT use qho_match_abbrev_tac`P res st'` before drule_then switch_BoolV_post. The abbreviation hides the switch_BoolV equation from first_assum/drule resolution, causing FIRST_ASSUM to fail. Instead: use drule toplevel_value_typed_BoolTV >> Cases_on b directly, then gvs[switch_BoolV_def, return_def] + metis_tac[return_state, raise_state].
works_when: Any branch using switch_BoolV_post after evaluating a boolean expression
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17676_t001

## L0607 scope='global' tags=audit,cheat,grep,verification
shape: Always run fresh grep audits before claiming completion
pattern: Never trust stale observations about cheat counts. Before proposing task completion: (1) grep 'cheat' in all in-scope .sml files, (2) grep 'suspend' in same, (3) grep '\[oracles:' in .Theory.txt files, (4) holbuild full target, (5) check for 'CHEAT' in holbuild output warnings. The semantics/prop/ directory has ~80+ cheats across 3 in-scope files (vyperTypeBuiltinsScript.sml, vyperTypeStmtSoundnessScript.sml, vyperTypeCallSoundnessScript.sml).
works_when: Auditing for task completeness before end_session proposal
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m17769_t002

## L0623 scope='C1.1' tags=value_has_type,type_value,iff,simp,boundary_lemma
shape: value_has_type at known type_value iff rewrite constrains value constructor
pattern: When the type_value is concretely known (from evaluate_type_def simplification), iff lemmas constrain the value constructor: value_has_type (BaseTV (UintT n)) v ⇔ ∃i. v = IntV i ∧ 0 ≤ i ∧ Num i < 2**n, value_has_type (BaseTV (IntT n)) v ⇔ ∃i. v = IntV i ∧ within_int_bound (Signed n) i, value_has_type (BaseTV DecimalT) v ⇔ ∃d. v = DecimalV d ∧ within_int_bound (Signed 168) d, value_has_type (BaseTV BoolT) v ⇔ ∃b. v = BoolV b, value_has_type (FlagTV m) v ⇔ ∃k. v = FlagV k ∧ k < 2**m. These are already [local,simp] in vyperTypeBuiltinsScript.sml as vht_BaseTV_* and vht_FlagTV. They let gvs derive value constructors from value_has_type assumptions.
works_when: Type_value is concretely known after evaluate_type_def simplifies; need to derive value constructors for evaluate_binop matching
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:68-123

## L0661 scope='C1.1' tags=value_has_type,ArrayTV,forward-only,not_iff
shape: value_has_type (ArrayTV tv bd) v is NOT iff v = ArrayV av
pattern: value_has_type (ArrayTV tv bd) v requires v to be ArrayV with specific inner variant: SArrayV for Fixed, DynArrayV for Dynamic, and additional conditions (sparse_has_type, all_have_type, LENGTH bounds). The iff lemma exists only for specific bounds: vht_ArrayTV_Fixed and vht_ArrayTV_Dynamic in vyperBuiltinTypingScript. A forward-only vht_ArrayTV_exists: value_has_type (ArrayTV tv bd) v ⇒ ∃av. v = ArrayV av is provable. ArrayV(TupleV vs) matches TupleTV not ArrayTV.
works_when: Need to extract ArrayV constructor from value_has_type (ArrayTV tv bd) v assumption; DO NOT claim iff with just ArrayV
evidence:
- source:semantics/prop/vyperTypingScript.sml:107-111
- source:semantics/prop/vyperBuiltinTypingScript.sml:556-568

## L0675 scope='C1.1' tags=COND_CASES_TAC,THEN1,subgoal,mp_tac,assumption_to_conclusion
shape: Use >> (THEN) not >- (THEN1) for tactics after COND_CASES_TAC when both branches need simp
pattern: CRITICAL: After COND_CASES_TAC creates two subgoals, >- simp[] only applies simp to the FIRST subgoal. The second subgoal never gets simplified. This means goals like `bounded_int_op ... ≠ INR(TypeError msg)` that should be closed by [local,simp] helpers remain unsolved. FIX: Use >> simp[] to apply simp to ALL subgoals, or add >> simp[] after the rpt block. This applies when conditionals in the conclusion need splitting and both branches are independently solvable by simp.
works_when: Any proof using COND_CASES_TAC or CASE_TAC where both branches should be solvable by simp, especially after mp_tac moves an assumption equation to the conclusion
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m18957_t001

## L0680 scope='C1.1' tags=COND_CASES_TAC,THEN1,THEN,subgoal,simp
shape: After COND_CASES_TAC, use >> simp[] not >- simp[] when both branches should be solved
pattern: After COND_CASES_TAC creates two subgoals, >> simp[] applies simp to ALL subgoals. Using >- simp[] (THEN1) only solves the FIRST subgoal, leaving the second unsolved. This is critical when the second subgoal (e.g., bounded_int_op ≠ TypeError) should be closed by [local,simp] helpers. The >> simp[] fix closed 10 of 14 remaining goals in well_typed_binop_no_type_error.
works_when: Any proof using COND_CASES_TAC or case splits where both branches are independently solvable by simp, especially after mp_tac moves an equation to the conclusion
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m18957_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19031_t001

## L0681 scope='C1.1' tags=TypeError,RuntimeError,binop,error_type,catch_all,diagnostic
shape: msg ≠ 'binop' goal after expanding evaluate_binop_def with well-typed inputs
pattern: If after expanding evaluate_binop_def with well-typed inputs you see a goal like msg ≠ 'binop', it means evaluate_binop produced INR(TypeError 'binop') - the catch-all fallback. This ONLY happens when the bop constructor or value constructors don't match any pattern in evaluate_binop_def. Do NOT try to prove msg ≠ 'binop' by tactics - instead find WHICH pattern didn't match and fix it (usually a stale constructor name in the typing definition).
works_when: Diagnosing residual goals in case-split proofs of no-TypeError theorems for evaluate_binop or similar functions with catch-all | _ => INR(TypeError msg) branches
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19031_t001
- source:syntax/vyperASTScript.sml:56-82
- source:semantics/prop/vyperTypeSystemScript.sml:89-92

## L0686 scope='global' tags=
shape: replace_text failure: use edit_lines with line numbers instead of retrying
pattern: When replace_text fails to match, stop immediately. Use git diff to check state, read_file for exact line content, then edit_lines with explicit start/end line numbers for the replacement. Never retry replace_text more than once with same text.
works_when: Tool call text matching fails in source files
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml

## L0690 scope='C1.1' tags=within_int_bound,signed_int_mod,int_mod,Num_int_lt,boundary_lemma
shape: signed_int_mod and integer % preserve within_int_bound; Num/int bridge via Num_int_lt
pattern: Three [local] helpers proved in vyperTypeBuiltinsScript.sml: within_int_bound_signed_int (iff rewrite for Signed bound), signed_int_mod_within_bound (0<m => within_int_bound(Signed m)(signed_int_mod m i)), int_mod_unsigned_within_bound (0<m => within_int_bound(Unsigned m)(i % &(2**m))). Num/int bridge: for goals Num(int_expr) < nat, use irule vyperArithTheory.Num_int_lt then simp[integerTheory.INT_OF_NUM]. int_mod is NOT a HOL definition - it is built-in integer %, no int_mod_def.
works_when: Proving value_has_type for wrapped/shift binop results where evaluate_binop produces signed_int_mod or int_mod
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:579-666

## L0695 scope='C1.1' tags=TRY,gen_tac,gvs,AllCaseEqs,forall_elimination
shape: After gvs with AllCaseEqs, some goals may lose their leading forall, so gen_tac fails
pattern: When using gvs with AllCaseEqs() and type/value inversion lemmas, some goals have all their variables resolved by simplification, leaving no leading universal quantifier. Then gen_tac fails with 'not a forall'. Fix: use TRY gen_tac >> instead. This is safe because gen_tac is only needed when there are remaining foralls.
works_when: After aggressive gvs in case-split proofs where some subgoals have fully-resolved type variables
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19446_t006

## L0696 scope='C1.1' tags=gvs,Excl,evaluate_binop,bounded_int_op,inversion_lemma,assumption_expansion
shape: gvs expands definitions in assumptions; use Excl to prevent over-expansion so inversion lemmas can match
pattern: When using gvs[evaluate_binop_def, ...] to expose bounded_int_op/wrapped_int_op calls in assumptions for inversion lemma matching, MUST use Excl 'bounded_int_op_def', Excl 'bounded_decimal_op_def', Excl 'wrapped_int_op_def' to prevent gvs from expanding those definitions too (which would prevent the inversion lemma from matching). Without Excls: 86 goals remain. With Excls: 37 goals remain.
works_when: Proving theorems about evaluate_binop results where you need to apply inversion lemmas like bounded_int_op_INL, bounded_decimal_op_INL, wrapped_int_op_INL
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19481_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:699-703

## L0700 scope='C1.1' tags=builtin_app,success_type,direct_proof,suspend_broken
shape: well_typed_builtin_app_success_type: 38 subgoals after Cases_on blt + gvs[well_typed_builtin_app_def, AllCaseEqs(), evaluate_type_def]
pattern: well_typed_builtin_app_success_type produces 38 subgoals (including Abs_int/Abs_decimal cases not in original suspend list). Direct proof with >- dispatch: for each subgoal, use simp[evaluate_builtin_def, value_has_type_def] (NOT gvs with AllCaseEqs inside >-). Not_bool: gvs[is_bool_type_def, evaluate_type_def] >> Cases_on y >> simp[evaluate_builtin_def, value_has_type_def]. Neg/Abs_decimal: imp_res_tac bounded_decimal_op_INL >> gvs[]. Env: drule Env_builtin_success_type. Acc: drule_all Acc_builtin_sound. Bop: irule well_typed_binop_success_type after gvs[evaluate_builtin_def]. Cheats remain for: AsWeiValue, Concat, Slice, MakeArray, ECRecover, ECAdd, ECMul.
works_when: Proving well_typed_builtin_app_success_type or similar multi-constructor builtin result-typing theorem
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19586_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:841-992

## L0702 scope='C1.1' tags=gvs,AllCaseEqs,subgoal_count,direct_proof
shape: gvs with AllCaseEqs() inside >- subgoal handler creates unexpected subgoals
pattern: When using >- (THEN1) to solve a single subgoal, do NOT use gvs[AllCaseEqs()] inside it - AllCaseEqs splits case expressions creating multiple subgoals that >- cannot handle. Instead: use simp (conclusion only), or use targeted Cases_on before gvs, or use gvs without AllCaseEqs. If AllCaseEqs is needed, handle ALL resulting subgoals with >> (applies to all) rather than >- (requires exactly one solved).
works_when: Writing direct proof with >- dispatch per subgoal where definitions contain case expressions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19591_t001

## L0703 scope='C1.1' tags=two-phase,gvs,AllCaseEqs,evaluate_type_def,evaluate_builtin_def,type_classifier
shape: Two-phase gvs for per-Constructor proofs: Phase1 classify + Phase2 resolve
pattern: For proofs with Cases_on constructor then per-branch resolution of evaluate_*_def: Phase1 gvs[well_typed_*_def, Excl type_classifier_catch_alls, is_*_type_inv lemmas] WITHOUT AllCaseEqs, evaluate_type_def, or evaluate_builtin_def. This produces clean goals with value_has_type tv v conclusion. Phase2: per-branch gvs[evaluate_type_def, evaluate_builtin_def] which case-splits value constructors against evaluate_builtin patterns, and the local [simp] vht_BaseTV_* iff lemmas auto-close many goals. AllCaseEqs in Phase1 creates misaligned >- chains and huge goals from evaluate_type expansion.
works_when: Proving well_typed_builtin_app_success_type, well_typed_builtin_app_no_type_error, or any theorem where well_typed_*_def constrains types but evaluate_*_def needs per-branch value constructor case analysis
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19668_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19675_t001

## L0704 scope='C1.1' tags=is_bytes_or_string_type,inversion_lemma,Excl,type_classifier
shape: is_bytes_or_string_type_def has [simp] catch-all; use Excl + inversion lemma
pattern: is_bytes_or_string_type_def has [simp] catch-all: is_bytes_or_string_type _ = F. Like all other type classifiers, this incorrectly fires on free variables. Add Excl is_bytes_or_string_type_def to gvs, and use inversion lemma is_bytes_or_string_type_inv: is_bytes_or_string_type ty <=> (?m. ty = BaseT (StringT m)) ∨ (?bd. ty = BaseT (BytesT bd)). Already added to vyperTypeBuiltinsScript.sml as [local] lemma.
works_when: Any proof where is_bytes_or_string_type has a free variable argument (e.g., after well_typed_builtin_app_def expands to give is_bytes_or_string_type h where h is free)
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:209-216
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19668_t001

## L0705 scope='C1.1' tags=builtin_app,success_type,two_phase_gvs,per_branch
shape: well_typed_builtin_app_success_type: two-phase gvs with per-branch TRY dispatch
pattern: For well_typed_builtin_app_success_type and similar multi-constructor proofs: Phase1 = Cases_on blt >> gvs[well_typed_builtin_app_def, Excl type_classifier_catch_all_defs, inversion lemmas] (NO AllCaseEqs, NO evaluate_type_def, NO evaluate_builtin_def). This produces clean value_has_type tv v goals. Phase2 = gvs[evaluate_type_def] resolves type_values. Phase3 = per-branch gvs[evaluate_builtin_def] + TRY dispatch: Not_bool (simp), Not_int_unsigned (gvs[type_to_int_bound_def,is_Unsigned_def]+arithmetic), Not_flag (w2n_and_low_mask_lt), Neg_int (bounded_int_op_INL), Neg_decimal (bounded_decimal_op_INL), Keccak256/Sha256 (LENGTH lemmas), Bop (irule well_typed_binop_success_type), Env (irule Env_builtin_success_type), Acc (drule_all Acc_builtin_sound), Floor/Ceil (floor/ceil helpers), AsWeiValue (evaluate_as_wei_value_def). Remaining hard: Concat, Slice, MakeArray, EC ops.
works_when: Proving well_typed_builtin_app_success_type or no_type_error with many builtin constructors that need different per-branch proof strategies
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19668_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19675_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:859-897

## L0706 scope='C1.1' tags=builtin_app,Abs,missing_constructor
shape: Abs builtin constructor exists in well_typed_builtin_app_def and evaluate_builtin_def but was missing from early PLAN estimates
pattern: The Abs builtin constructor is defined: well_typed_builtin_app ty Abs ts = (ts = [ty] /\ is_numeric_type ty). evaluate_builtin for Abs is NOT in evaluate_builtin_def - it falls through to the catch-all INR(TypeError 'builtin'). This means either (1) Abs has no evaluate_builtin clause yet and should be excluded from the success_type theorem via blt <> Abs, or (2) Abs evaluation needs adding. Check if Abs is actually implemented before proving its success_type. If not implemented, the well_typed_builtin_app_success_type theorem needs blt <> Abs premise like it already has blt <> Len.
works_when: Proving well_typed_builtin_app_success_type or no_type_error when encountering Abs constructor goals
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:213
- source:semantics/vyperContextScript.sml:365-451

## L0711 scope='C1.1' tags=decimal,word_arithmetic,word_quot,w2i,floor_division
shape: Decimal Mul/Div/Mod inline word operations in evaluate_binop_def
pattern: evaluate_binop_def has inline word-level operations for decimal arithmetic: Decimal Mul uses w2i(word_quot(i2w p) 0x2540BE400w) where 0x2540BE400w = 10000000000w, Decimal Div uses bounded_decimal_op(w2i(word_quot(i2w(i1*10000000000)) (i2w i2))), Decimal Mod uses bounded_decimal_op(w2i(word_rem(i2w i1)(i2w i2))). These create word-level goals that need dedicated boundary lemmas relating w2i(word_quot/word_rem ...) to integer floor_div/mod. Existing helpers: floor_decimal_in_int256_bounds, ceil_decimal_in_int256_bounds (in vyperTypeBuiltinsScript.sml ~line 832). Need a lemma: within_int_bound (Signed 168) (ABS p / 10000000000) ==> within_int_bound (Signed 168) (w2i (word_quot (i2w p) (10000000000w:bytes32))).
works_when: Proving success-typing for decimal Mul/Div/Mod binop results where evaluate_binop_def inline word ops need to be connected to within_int_bound
evidence:
- source:semantics/vyperValueOperationScript.sml:234-236
- source:semantics/vyperValueOperationScript.sml:251-254
- source:semantics/vyperValueOperationScript.sml:286-289
- source:semantics/prop/vyperTypeBuiltinsScript.sml:832-854

## L0714 scope='C1.1' tags=decimal,word_quot,within_int_bound,boundary_lemma,int_div_lt_imp
shape: decimal_mul_word_bound: within_int_bound(Signed 168)(ABS p / 10^10) ==> within_int_bound(Signed 168)(w2i(i2w p / 10^10w))
pattern: decimal_mul_word_bound bridges the gap between integer-level within_int_bound and word-level w2i(word_quot...) that evaluate_binop_def uses for Decimal Mul. The proof chain: (1) ABS p / 10^10 < 2^167 (from Signed 168 bound), (2) ABS p < 2^167 * 10^10 < 2^255 (via int_div_lt_imp), (3) within_int_bound(Signed 256) p so w2i(i2w p) = p, (4) integer_wordTheory.word_quot gives i2w(p quot 10^10), (5) ABS(p quot 10^10) = ABS p / 10^10 (integer division properties), (6) within_int_bound(Signed 168)(p quot 10^10) from hypothesis, (7) w2i(i2w(p quot 10^10)) = p quot 10^10. This lemma exists in vyperTypeSoundnessHelpersScript.sml:6185 as [local]. Must be ported to vyperTypeBuiltinsScript.sml before the binop proof. Also needs int_div_lt_imp (same file, line 6164).
works_when: Bridging w2i(word_quot(i2w p)(10^10w:bytes32)) to integer-level ABS p / 10^10 in success-typing proofs for Decimal Mul binop
evidence:
- source:semantics/prop/vyperTypeSoundnessHelpersScript.sml:6185-6240
- source:semantics/prop/vyperTypeSoundnessHelpersScript.sml:6164

## L0715 scope='C1.1' tags=wrapped_int_op,int_bound_bits,0_less,premise_order,AllCaseEqs
shape: wrapped_int_op_INL requires 0 < int_bound_bits u derived BEFORE gvs[AllCaseEqs()] that resolves u
pattern: wrapped_int_op_INL[local]: 0 < int_bound_bits u /\ wrapped_int_op u r = INL v ==> ?i. v = IntV i /\ within_int_bound u i. After gvs[AllCaseEqs()] inside the binop proof, the type variable u gets resolved by Cases_on from the unsigned/signed split, but the required 0 < int_bound_bits u premise may be lost because gvs performs variable elimination. FIX: derive 0 < int_bound_bits u BEFORE expanding evaluate_binop_def, or handle wrapped-op bop cases in separate TRY blocks where u is still available. For well_typed types: evaluate_type returns well-formed type_values with n > 0 for int types, so int_bound_bits u > 0 follows from well_typed_binop premises.
works_when: Proving success_type for wrapped operations (UnsafeAdd/Sub/Mul/Div) where AllCaseEqs() variable elimination removes the bound variable needed by wrapped_int_op_INL
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:718-726
- tool_output:TO_type_system_rewrite-20260516T153850Z_m19940_t002

## L0719 scope='C1.1' tags=well_typed_binop_success_type,per-family,26_goals,helper_map
shape: well_typed_binop_success_type 26 remaining goals map to 7 helper families
pattern: After Cases_on bop + gvs[well_typed_binop_def, is_*_inv, evaluate_type_def, type_to_int_bound_def, AllCaseEqs()] resolves type/value, the 26 remaining goals split into: (1) Decimal Mul (1 goal): decimal_mul_word_bound bridges w2i(word_quot(i2w p)/10^10w) to within_int_bound(Signed 168). (2) Wrapped UAdd/USub/UMul (6 goals): wrapped_int_op_INL_Unsigned/Signed gives existential i with bound. (3) Wrapped UForceDiv/SForceDiv (2 goals): same + word_quot/word_rem bridge. (4) ExpMod (1 goal): w2n(word_exp...) < 2^256 via w2n_lt. (5) Flag And/Or/Xor (3 goals): int_bitwise_nat_bound gives Num result < 2^m. (6) ShL (3+ goals): evaluate_binop uses int_mod r &(2^n) for unsigned and signed_int_mod b r for signed - use int_mod_unsigned_within_bound and signed_int_mod_within_bound (already [local]). (7) ShR (3+ goals): int_shift_right_within_bound (Signed) and int_shift_right_unsigned_within_bound.
works_when: Proving well_typed_binop_success_type or any per-operator integer arithmetic result-typing where evaluate_binop has inline word ops or wrapping
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20020_t002
- source:semantics/prop/vyperTypeSoundnessHelpersScript.sml:6185-6242
- source:semantics/vyperValueOperationScript.sml:303-317

## L0723 scope='C1.1' tags=imp_res_tac,drule,wrapped_int_op_INL,existential_conclusion
shape: imp_res_tac not drule for multi-antecedent theorem with existential conclusion
pattern: When a theorem has multiple antecedents and an existential conclusion (e.g., !u r v. 0 < int_bound_bits u /\ wrapped_int_op u r = INL v ==> ?i. v = IntV i /\ within_int_bound u i), use imp_res_tac not drule. drule matches only one antecedent and pushes a residual implication that simp cannot discharge through the existential. imp_res_tac resolves ALL antecedents simultaneously and adds the conclusion to assumptions, then gvs can unfold and close.
works_when: Proving inversion lemmas where the base theorem has /\-joined antecedents and ?-quantified conclusion
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20076_t001

## L0724 scope='C1.1' tags=ShL,shift_left,int_mod,signed_int_mod,evaluate_binop
shape: ShL evaluate_binop uses int_mod/signed_int_mod, not shift_left_bound
pattern: evaluate_binop_def for ShL: r = int_shift_left (Num i2) i1; then if is_Unsigned u then IntV (int_mod r &(2**b)) else IntV (signed_int_mod b r). NO int_bitwiseTheory.int_shift_left_bound exists. For unsigned, use int_mod_unsigned_within_bound; for signed, use signed_int_mod_within_bound. Both are already [local] in vyperTypeBuiltinsScript.sml.
works_when: Proving value_has_type for ShL binop results
evidence:
- source:semantics/vyperValueOperationScript.sml:303-309
- source:semantics/prop/vyperTypeBuiltinsScript.sml:699-715

## L0725 scope='C1.1' tags=conjunction,syntax,API,term_quotation
shape: Use /\ not / for HOL4 conjunction in term quotations; /\ works reliably through API
pattern: In HOL4 term quotations, /\ is conjunction and / is integer division. Through the API, both /\ and the Unicode /\ work but /\ is more reliable. The original bug was using / instead of /\ throughout all helper lemma statements. Always verify: after editing theorem statements, build immediately to catch parse errors.
works_when: Writing any HOL4 theorem statement or term quotation via tool calls
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:728-957

## L0727 scope='C1.1' tags=flag_bitwise,int_bitwise_nat_bound,PURE_REWRITE_TAC,qspecl_then
shape: Proving Num(int_and/or/xor(&k)(&k')) < 2**m from k<2**m /\ k'<2**m
pattern: For flag bitwise operator goals (And/Or/Xor on FlagV), unfold int_and/int_or/int_xor to BITWISE via PURE_REWRITE_TAC[int_bitwiseTheory.int_and_def/int_or_def/int_xor_def], then apply int_bitwise_nat_bound with the boolean function as first argument via qspecl_then. For And: qspecl_then [`$/\\`,k,k',m]. For Or: qspecl_then [`$\\/`,k,k',m]. For Xor: qspecl_then [`\\x y:bool. x <> y`,k,k',m]. The OLD helpers script (vyperTypeSoundnessHelpersScript.sml:6277-6288) has the working pattern.
works_when: Proving value_has_type for FlagV bitwise results where evaluate_binop produces Num(int_and/or/xor(&k)(&k')) from k < 2**m and k' < 2**m
evidence:
- source:semantics/prop/vyperTypeSoundnessHelpersScript.sml:6277-6288

## L0728 scope='C1.1' tags=irule,conjunction,partial_match,mp_tac,int_bitwise
shape: irule fails when lemma concludes A/\B but goal only has B; use mp_tac+strip_tac instead
pattern: When a boundary lemma concludes a conjunction (e.g., `0 <= X /\ Num X < 2**k`) but the goal only has one conjunct (e.g., `Num X < 2**m`), irule cannot match. Fix: (1) use `mp_tac lemma >> strip_tac >> asm_rewrite_tac[]` instead, (2) prove a separate lemma for just the needed conjunct (e.g., `int_bitwise_nat_bound_lt`), or (3) use `drule` if antecedents match assumptions. The reference implementation in vyperTypeSoundnessHelpersScript.sml:6277-6288 uses `qspecl_then [..] mp_tac int_bitwise_nat_bound >> ASM_REWRITE_TAC[] >> strip_tac >> ASM_REWRITE_TAC[]`.
works_when: Proving value_has_type for flag/binop results where the bound lemma concludes both 0<=... and Num...<2**k but only the < part remains in the goal
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20154_t001 - Goals 2-4: Num(int_bitwise $/\ ...) < 2**m only
- source:semantics/prop/vyperTypeSoundnessHelpersScript.sml:6277-6288

## L0729 scope='C1.1' tags=within_int_bound,GSYM,simp_folding,value_has_type,expanded_form
shape: simp[GSYM within_int_bound_def] does NOT re-abstract 0<=i/\Num i<2**n back to within_int_bound form
pattern: After gvs[AllCaseEqs(), value_has_type_def], within_int_bound gets expanded to 0<=i/\Num i<2**n (for Unsigned) or to int_bound form (for Signed). Adding Excl 'within_int_bound_def' does NOT prevent this because the expansion comes from value_has_type_def, not directly. simp[GSYM within_int_bound_def] also fails to fold back because within_int_bound_def is a multi-clause conditional definition that simp cannot match backwards when the bound constructor is known. Work with the expanded form directly: prove bridge lemmas that conclude in the exact expanded goal shape, or use irule/apply_tac on lemmas that match the expanded conjunction.
works_when: Any proof where gvs[value_has_type_def] or similar expands within_int_bound and you want to re-abstract or apply with_int_bound-concluding lemmas
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20153_t001 - ShR goals 5-6 remain expanded despite simp[GSYM within_int_bound_def]

## L0730 scope='C1.1' tags=ExpMod,w2n_lt,word_exponentiation,dimword
shape: w2n(word_exp) < 2**256: use irule w2n_lt then simp[dimword_def], may need type instantiation
pattern: For ExpMod goal `w2n (i2w i ** i2w i') < 2**256`: this is `w2n w < dimword(:256)` for any `:256` word `w`. Use `irule wordsTheory.w2n_lt` then `simp[wordsTheory.dimword_def]`. If irule fails due to type ambiguity, try `irule_at Any wordsTheory.w2n_lt` or `simp[wordsTheory.w2n_lt, wordsTheory.dimword_def]` directly. The word exponentiation `**` on `:256` words always produces a `:256` word, so `w2n` of the result is < `dimword(:256)` = 2^256.
works_when: Proving w2n of a word operation result bounded by dimword, especially for ExpMod/modexp
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20154_t001 - Goal 1: w2n(i2w i ** i2w i') < 2^256

## L0731 scope='C1.1' tags=Min,Max,within_int_bound,IF_CASES_TAC,min_max,binop
shape: Min/Max binop success: case split on i<i' then qexists the smaller/larger value
pattern: Goals of form `∃i''. (i < i' ∧ i = i'' ∨ ¬(i < i') ∧ i' = i'') ∧ within_int_bound (Signed n) i''` (Min) or `∃i''. (i < i' ∧ i' = i'' ∨ ¬(i < i') ∧ i = i'') ∧ within_int_bound (Signed n) i''` (Max) need: `IF_CASES_TAC 'i < i'' >> qexists_tac 'i' >> simp[] >- qexists_tac 'i' >> simp[]`. Both witnesses are within_int_bound since either i or i' is chosen, and both come from within_int_bound assumptions. For decimal Min/Max, same pattern with d/d'.
works_when: Proving Min/Max result typing in well_typed_binop_success_type or similar
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20154_t001 - Goals 8-11

## L0732 scope='C1.1' tags=Num,int,INT_OF_NUM,nonnegative,bridge_lemma
shape: Goal: Num (int_expr) < 2 ** n with assumptions 0 <= int_expr and int_expr <= i and Num i < 2 ** n
pattern: Prove Num (int_expr) < 2 ** n by converting int_expr = &(Num int_expr) and i = &(Num i) via INT_OF_NUM (since both are non-negative), then use GSYM INT_OF_NUM_LE to turn <= into Num ... <= Num ..., then decide_tac/arithmetic.
works_when: Both int_expr and i are non-negative integers (type :int) and you need to convert int inequality to Num inequality
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:938-951

## L0733 scope='C1.1' tags=gvs,conjunct,side_effect,conjunction
shape: Goal after gvs[]: conjunction partially resolved when one conjunct was already an assumption
pattern: After gvs[] with assumptions like 0 <= X already present, gvs may remove the first conjunct from 0 <= X /\ Num X < bound, leaving just Num X < bound. Do NOT follow with conj_tac; proceed directly to the remaining subgoal.
works_when: gvs[] or similar simplification that can match and eliminate conjuncts against existing assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20203_t001

## L0734 scope='C1.1' tags=w2n,dimword,2^256,large_number,word
shape: Goal: w2n (word_expr) < LARGE_CONSTANT where LARGE_CONSTANT = 2 ** 256 already computed
pattern: w2n_lt concludes w2n w < dimword(:a), but dimword(:256) = 2 ** dimindex(:256) = 2 ** 256. If the goal has the explicit computed constant for 2**256 (e.g., 115792089237316195423570985008687907853269984665640564039457584007913129639936), you need simp[numLib.NUMERAL, numLib.ARITH_ss, wordsTheory.dimword_def] or EVAL_TAC to unify. Simpler: prove the bridge lemma with dimword(:256) and use CONV_TAC in the main proof, OR just use repeat CASE_TAC with simp[w2n_lt, dimword_def].
works_when: The goal contains a 2^256-sized constant from value_has_type_def expansion that must match a lemma concluding 2 ** 256 or dimword(:256)
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20174_t002

## L0735 scope='global' tags=dimword,w2n_lt,irule
shape: Proving w2n (word_expr) < 2 ** 256 using w2n_lt
pattern: When proving w2n (w:256 word) < 2**256, irule w2n_lt fails because 2**256 is a computed numeral. Fix: state the lemma as w2n w < dimword(:256) and prove via irule w2n_lt. If the consumer needs 2**256, add dimword_def + EVAL dimindex(:256) at the call site.
works_when: Word size bounds where 2**n would be computed to a large numeral
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20266_t001

## L0736 scope='global' tags=gvs,conjunction,conj_tac
shape: Goal is non-conjunctive after gvs[] that was originally a conjunction
pattern: After gvs[] with assumptions, gvs may resolve one conjunct from a conjunction in the goal, leaving only the other. Always add a FAIL_TAC probe after gvs to inspect the actual goal before using conj_tac or other structural tactics. If gvs already split the conjunction, proceed directly.
works_when: gvs[] in proofs that simplify goal conjunctions using assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20217_t002

## L0737 scope='global' tags=Num_int_lt,integer,monotonicity
shape: Proving Num i < bound from 0 <= i and i < j and Num j < bound
pattern: Use vyperArithTheory.Num_int_lt: 0 <= a /\ a < b ==> Num a < Num b. Combined with int_shift_right_nonneg_bounds (gives 0<= and <=), this bridges integer ordering to nat ordering for non-negative integers.
works_when: Converting integer < to Num < for non-negative integers, especially in within_int_bound unsigned range proofs
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20238_t001

## L0738 scope='global' tags=tool_limitation,backslash,SML,write_file
shape: Editing HOL4 SML files containing /\ operator
pattern: The replace_text and edit_lines tools strip backslashes from /\ (HOL4 ASCII conjunction), turning /\ into /. Always use write_file to rewrite the complete file when editing lines containing /\ or \/. This also affects \ within string literals.
works_when: Any SML file edit involving HOL4 logical operators /\, \/, ==>, or other backslash-containing syntax
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20368_t001 - edit_lines stripping /\ to /

## L0742 scope='C1.2' tags=
shape: Helper theorems from vyperBuiltinTyping are [local] and inaccessible from vyperTypeBuiltins
pattern: vyperBuiltinTypingScript.sml has proved helpers: evaluate_concat_typed, evaluate_slice_typed, evaluate_as_wei_value_typed, evaluate_ecrecover_typed, evaluate_ecadd_typed, evaluate_ecmul_typed - but ALL are marked [local]. vyperTypeBuiltinsScript.sml cannot import them. Must re-prove in vyperTypeBuiltins or add non-local versions to an intermediate theory. The success_type Resume cheats needing these: AsWeiValue_int, AsWeiValue_decimal, Concat_bytes, Concat_string, Slice_bytes, Slice_string, ECAdd, ECMul, MakeArray_tuple, MakeArray, and the ECRecover catch-all.
works_when: Proving success_type Resume branches that depend on evaluate_concat/evaluate_slice/evaluate_as_wei_value/EC helper typing
evidence:
- source:semantics/prop/vyperBuiltinTypingScript.sml:203-262

## L0744 scope='C1.2' tags=builtin,resume,FAIL_TAC,goal_state
shape: Resume block proofs after gvs in main theorem
pattern: Before writing tactics in Resume blocks, insert FAIL_TAC "probe" to see exact goal state. Variables get renamed by gvs in main Cases_on proof, so names from main context won't match. Work with actual variable names from probed goal.
works_when: Proving suspended Resume blocks where main proof does significant gvs simplification before suspending
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20641_t001

## L0745 scope='C1.1' tags=binop,priority,blocking
shape: well_typed_binop proofs block entire assignment chain
pattern: well_typed_binop_no_type_error and well_typed_binop_success_type (C1.1) are strict prerequisites for C2 assignment subscript soundness, blocking C3, C4, C6. Prioritize binop proofs over remaining builtin success_type branches. Binop proofs need Cases_on bop plus inversion lemmas like bounded_int_op_INL (in old vyperBuiltinTypingScript.sml as [local], needs re-proving in new stack).
works_when: Deciding what to prove next in C1 cluster
evidence:
- source:semantics/prop/vyperTypeStatePreservationScript.sml:1795

## L0746 scope='C1.1' tags=binop,TypeError,evaluate_binop,no_type_error
shape: well_typed_binop + value_has_type implies evaluate_binop never hits TypeError
pattern: evaluate_binop ONLY returns TypeError when value constructors don't match (e.g. IntV+BoolV). bounded_int_op/bounded_decimal_op return RuntimeError on overflow not TypeError. So if well_typed_binop constrains types and value_has_type constrains constructors, then both values match evaluate_binop patterns - no TypeError. Case-split on bop, use value_has_type_def to derive constructors, simplify evaluate_binop_def.
works_when: Proving well_typed_binop_no_type_error or binop soundness where TypeError must be ruled out
evidence:
- source:semantics/vyperValueOperationScript.sml:214-340
- source:semantics/prop/vyperTypeSystemScript.sml:85-125

## L0747 scope='C1.1' tags=binop,success_type,vyperEvalBinop
shape: Use vyperEvalBinopTheory per-constructor theorems for success_type
pattern: vyperEvalBinopTheory exports per-operator theorems: evaluate_binop_add/sub/mul, mod_unsigned/div_unsigned/div_signed/mod_signed, exp, and_int/or_int/xor_int, and_bool/or_bool/xor_bool, uadd/usub/umul/udiv, shl/shr, expmod, min/max, eq_int/eq_bool/noteq_int/noteq_bool, lt/lte/gt/gte. These give exact result shapes for success_type proofs.
works_when: Proving well_typed_binop_success_type or evaluate_binop result typing
evidence:
- source:semantics/prop/vyperEvalBinopScript.sml:1-413

## L0750 scope='C1.1' tags=binop,per-operator,evaluate_binop,vyperEvalBinop,INL
shape: Use vyperEvalBinopTheory per-operator theorems for binop success/no-TypeError proofs
pattern: vyperEvalBinopTheory exports evaluate_binop_add/sub/mul/div_unsigned/div_signed/mod_unsigned/mod_signed/exp/and_bool/or_bool/xor_bool/and_int/or_int/xor_int/uadd/usub/umul/udiv/shl/shr/expmod/min/max etc. These give INL(result) facts directly. For no-TypeError: after type/value resolution, each bop case matches a vyperEvalBinop lemma giving INL result, then INL ≠ INR(TypeError msg) is trivial. For success_type: each lemma gives the exact result value for value_has_type reasoning. This avoids expanding the 413-line evaluate_binop_def.
works_when: Proving well_typed_binop_no_type_error or well_typed_binop_success_type after type/value constructors are resolved from well_typed_binop_def and value_has_type iff lemmas
evidence:
- source:semantics/prop/vyperEvalBinopScript.sml
- episode:E0144
- episode:E0151

## L0751 scope='C1.1' tags=binop,no_type_error,proof_structure,disch_tac,forall_msg
shape: well_typed_binop_no_type_error proof: disch_tac preserves forall-msg, then Cases_on bop + gvs + gen_tac + per-operator dispatch
pattern: Correct proof structure for !msg. evaluate_binop ... ≠ INR(TypeError msg): (1) disch_tac to move antecedents to assumptions preserving the !msg quantifier (gvs would eliminate it incorrectly), (2) Cases_on bop >> gvs[well_typed_binop_def, is_*_type_inv, evaluate_type_def, type_to_int_bound_def, AllCaseEqs()] for type/value resolution, (3) gen_tac to strip the !msg, (4) per-operator: irule matching evaluate_binop_* lemma giving INL, then INL ≠ INR(TypeError msg) by constructor distinctness. For conditional branches (Div/Mod zero-check): COND_CASES_TAC >> simp[].
works_when: Proving no-TypeError theorems with universally-quantified error message disequations
evidence:
- episode:E0138
- episode:E0139
- episode:E0151
- source:semantics/prop/vyperTypeBuiltinsScript.sml:68-84

## L0752 scope='global' tags=file_corruption,write_file,restore,git
shape: Accidental write_file truncation of large HOL4 source files
pattern: When write_file overwrites a HOL4 source file, it destroys ALL content. Recovery: use git show HEAD:path to get committed version, then write_file to restore. If uncommitted changes existed, check git stash or reflog. ALWAYS read current file state before write_file. Prefer replace_text/edit_lines for targeted edits to avoid accidental truncation.
works_when: HOL4 source file accidentally truncated or overwritten
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml

## L0753 scope='C1.1' tags=binop,well_typed_binop_def,constructor_names,UnsafeAdd
shape: well_typed_binop_def stale constructor names vs bop Datatype
pattern: well_typed_binop_def had UAdd/USub/UMul/UDiv but bop Datatype uses UnsafeAdd/UnsafeSub/UnsafeMul/UnsafeDiv. After Cases_on bop, the Unsafe* cases dont match any well_typed_binop clause, falling to evaluate_binop catch-all INR(TypeError binop). Fix: replace UAdd->UnsafeAdd etc. in well_typed_binop_def. This was already fixed in vyperTypeSystemScript.sml:93-96 and builds successfully.
works_when: Cases_on bop produces unexpected INR(TypeError) goals for Unsafe* operators
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:93-96
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20746_t001

## L0754 scope='C1.1' tags=evaluate_binop,TypeError,RuntimeError,no_type_error
shape: evaluate_binop TypeError vs RuntimeError distinction
pattern: In evaluate_binop_def, TypeError ONLY appears in value-mismatch fallback branches (e.g. | _ => INR(TypeError binop)). All semantic errors (overflow, div-by-zero, negative shift) return INR(RuntimeError _). Since RuntimeError != TypeError by constructor distinctness, after type resolution ensures correct value constructors, no TypeError is reachable. This means well_typed_binop + value_has_type => no TypeError is structurally true without reasoning about arithmetic bounds.
works_when: Proving well_typed_binop_no_type_error or any lemma about evaluate_binop not returning TypeError
evidence:
- source:semantics/vyperValueOperationScript.sml:214-405

## L0755 scope='C1.1' tags=binop,inversion_lemma,simp,catch_all,is_int_type
shape: Type classifier [simp] catch-all rules lose cases when argument is a free variable
pattern: Add local inversion lemmas (is_int_type_inv, is_numeric_type_inv, is_bool_type_inv, is_flag_type_inv, is_comparable_type_inv) that expand classifiers to disjunctions of constructors. Use with Excl to suppress the catch-all [simp] rules: gvs[well_typed_binop_def, Excl "is_int_type_def", is_int_type_inv, ...]. Without these, gvs on e.g. is_int_type (BaseT b) fires the catch-all is_int_type _ = F and discards the correct UintT/IntT cases.
works_when: Any proof using type classifier predicates (is_int_type, is_numeric_type, is_bool_type, is_flag_type, is_comparable_type) where the argument is not yet fully resolved, especially after Cases_on bop where the type variable is still free.
evidence:
- episode:E0151
- source:semantics/prop/vyperTypeBuiltinsScript.sml:620-660

## L0756 scope='C1.1' tags=value_has_type,iff,simp,constraint,type_value
shape: value_has_type with known type_value constrains value constructor via iff lemma
pattern: Add local [simp] iff lemmas that directly rewrite value_has_type (BaseTV (UintT n)) v to ∃i. v = IntV i ∧ 0 ≤ i ∧ Num i < 2**n (and similarly for IntT, DecimalT, BoolT, FlagTV, StringT, BytesT, AddressT). These avoid the need for Cases_on v >> gvs[value_has_type_inv] which creates 10+ subgoals from value constructor split. The iff lemmas match the specific type and constrain value directly.
works_when: The type_value is concretely known (from evaluate_type_def simplification or assumption). Used before expanding evaluate_binop_def so that value constructors are resolved by the time fallback branches are checked.
evidence:
- episode:E0151
- source:semantics/prop/vyperTypeBuiltinsScript.sml:620-660
- source:semantics/prop/vyperTypeBuiltinsScript.sml:vht_BaseTV_*

## L0757 scope='C1.1' tags=Excl,gvs,bounded_int_op,wrapped_int_op,within_int_bound,opaque
shape: Keep bounded/wrapped/within_int_bound opaque during gvs then re-abstract for inversion lemmas
pattern: In well_typed_binop_success_type and similar proofs: gvs[evaluate_binop_def, AllCaseEqs(), value_has_type_def, Excl "bounded_int_op_def", Excl "bounded_decimal_op_def", Excl "wrapped_int_op_def", Excl "within_int_bound_def", LET_THM] keeps these operations as opaque equation assumptions. Then simp[GSYM within_int_bound_def] re-abstracts the expanded within_int_bound goals so imp_res_tac bounded_int_op_INL / wrapped_int_op_INL can match. Without the Excls, gvs expands everything and the INL inversion lemmas cannot match.
works_when: Proofs that need to invert INL results from bounded_int_op, bounded_decimal_op, wrapped_int_op where the result type depends on within_int_bound.
evidence:
- episode:E0147
- episode:E0151
- source:semantics/prop/vyperTypeBuiltinsScript.sml:well_typed_binop_success_type proof

## L0758 scope='global' tags=git_stash,lost_edits,file_recovery
shape: When dossier says proved but source has cheat, check git stash for lost edits
pattern: If a dossier episode claims a component was proved (result='proved') but the current source still has cheat for that theorem, the edits may be in a git stash. Run: git stash list, git show stash@{N}:path/to/file | wc -l (compare line count). If the stash has a larger file with the proved version, use git show stash@{N}:path > content then write_file to restore. This recovers entire proved file contents in one step instead of reproving from scratch.
works_when: Previous session proved theorems but edits were lost due to context clear, failed commit, accidental overwrite, or git reset.
evidence:
- episode:E0151
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20876_t001

## L0763 scope='C1.2' tags=builtin,helper_lemma,irule,decomposition
shape: Per-constructor helper lemmas for well_typed_builtin_app proofs
pattern: For well_typed_builtin_app_no_type_error and success_type: decompose into per-constructor helper lemmas (flag_Not_no_type_error, as_wei_value_uint_no_type_error, concat_bytes/string_no_type_error, slice_bytes/string_no_type_error, make_array_no_type_error, ecrecover/ecadd/ecmul_no_type_error). Each helper takes specific well_typed_builtin_app premises + evaluate_type/value_has_type assumptions and proves the no-TypeError conclusion. Main theorem uses irule with these helpers after Cases_on blt. Avoid broad gvs[evaluate_type_def] in the main theorem.
works_when: Proving multi-constructor builtin soundness theorems where each constructor has different proof structure
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m20999_t002

## L0764 scope='C1.2' tags=builtin,Not,flag,value_has_type_iff
shape: Flag Not no-TypeError proof: value_has_type iff lemma resolves tv then evaluate_builtin_def simplifies
pattern: For flag_Not_no_type_error: first derive tv = FlagTV m from value_has_type tv y (using the FlagTV iff lemma), then expand evaluate_builtin_def which uses evaluate_type ... = SOME tv to resolve the case expression to INL (FlagV ...). The FlagV result is trivially not INR (TypeError msg). Use context_well_typed to get FLOOKUP (get_tenv cx) facts if needed for evaluate_type_def expansion.
works_when: Proving flag Not/AsWeiValue/other builtin cases where evaluate_type result constrains the branch
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21029_t001

## L0765 scope='C1.2' tags=builtin,evaluate_type,evaluate_builtin,simplification_order,joint_expansion
shape: Joint expansion of evaluate_type_def with evaluate_builtin_def for case-elimination
pattern: When evaluate_builtin_def contains 'case evaluate_type ... of' and there is an assumption 'evaluate_type ... = SOME tv': expand evaluate_type_def and evaluate_builtin_def IN THE SAME simp/gvs call so the simplifier resolves the case expression using the SOME assumption. For helper lemmas where ty constrains tv: (1) gvs[evaluate_type_def] to resolve tv, (2) gvs[vht_*] to constrain value from value_has_type, (3) simp/expand evaluate_builtin_def (optionally with evaluate_type_def again if case evaluate_type remains).
works_when: Proving helper lemmas where evaluate_builtin_def has case evaluate_type and the evaluate_type result is available as an assumption
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21069_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21034_t002

## L0766 scope='C1.2' tags=builtin,value_has_type,vht,iff,constructor_constraint
shape: Use vht_* iff lemmas to constrain value constructors from value_has_type before expanding builtin defs
pattern: When a helper has 'value_has_type tv v' where tv is resolved to a concrete typed_value (e.g. BaseTV (UintT n)), use gvs[vht_BaseTV_UintT] to reduce 'value_has_type (BaseTV (UintT n)) v' to exists i. v = IntV i /\ 0 <= i /\ Num i < 2 ** n. This eliminates impossible Cases_on v subgoals. Available: vht_BaseTV_UintT, vht_BaseTV_IntT, vht_BaseTV_DecimalT, vht_BaseTV_BoolT, vht_FlagTV, vht_BaseTV_StringT, vht_BaseTV_BytesT_Fixed, vht_BaseTV_BytesT_Dynamic, vht_BaseTV_AddressT.
works_when: Proving builtin helpers where value_has_type with known typed_value constrains the value constructor
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21034_t002

## L0767 scope='C1.2' tags=denomination,case_expression_in_goal,AsWeiValue,ARITH_TAC
shape: Case expressions on free variables in goal block ARITH_TAC
pattern: When goal contains case dn of Wei => 1 | Kwei => 1000 | ... (case on free variable), intLib.ARITH_TAC fails. Fix: Cases_on the free variable first to resolve case expression to concrete number.
works_when: Proving builtin helpers with evaluate_as_wei_value or similar case expressions on denomination/type-name variables
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21034_t002

## L0768 scope='C1.2' tags=list,Cases_on,empty_case
shape: List case split needs >- for empty case before Cases_on head
pattern: After Cases_on vs (list variable), two subgoals: vs=[] and vs=h::t. If subsequent tactics reference h, fails on empty subgoal. Fix: use >- (gvs[LIST_REL_NIL] or similar) to dispatch empty case, then continue on cons case.
works_when: Proving builtin helpers that case-split on list variables before working on list elements
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21034_t002

## L0769 scope='C1.2' tags=LIST_REL,value_has_type,BytesV,StringV,constructor_constraining
shape: LIST_REL value_has_type tvs vs + EVERY (?bd. t = BaseT (BytesT bd)) ts => EVERY (?bs. v = BytesV bs) vs
pattern: When proving ALL list elements have a specific value constructor from LIST_REL value_has_type + EVERY type constraint, first prove the EVERY constructor lemma as a separate helper BEFORE doing Cases_on any value variable. This avoids impossible subgoals where value_has_type tv v has tv unconstrained. Pattern: Induct >> rw[LIST_REL_CONS1, LIST_REL_NIL] >> Cases_on type variant (e.g. bd for BytesT Fixed/Dynamic) >> gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on value >> gvs[value_has_type_def].
works_when: Proving ALL list elements have a specific value constructor when LIST_REL value_has_type constrains types.
evidence:
- source:semantics/prop/vyperBuiltinTypingScript.sml:755-779
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21146_t001

## L0770 scope='C1.2' tags=Concat,evaluate_concat,LENGTH,well_typed_builtin_app
shape: concat_no_type_error with 2 <= LENGTH vs
pattern: well_typed_builtin_app for Concat n requires 2 <= LENGTH ts. evaluate_concat_def checks NULL vs OR NULL (TL vs) returning TypeError if true. Therefore concat helper theorems MUST include 2 <= LENGTH vs premise. Main theorem derives this via irule concat_no_type_error >> gvs[] which resolves LENGTH from LIST_REL_LENGTH.
works_when: Concat builtin soundness proofs where static typing guarantees minimum 2 arguments.
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21146_t001
- source:semantics/prop/vyperTypeSystemScript.sml:176-179

## L0771 scope='C1.2' tags=LIST_REL,bridge_lemma,interface_mismatch,drule
shape: LIST_REL value_has_type tvs vs + MAP evaluate_type ts = MAP SOME tvs
pattern: When consumer interface uses LIST_REL value_has_type tvs vs with separate MAP equality, but helper theorems use combined LIST_REL (λv t. ∃tyv. evaluate_type tenv t = SOME tyv ∧ value_has_type tyv v) vs tys, add a bridge lemma LIST_REL_value_has_type_imp_combined and use forward reasoning: drule bridge >> disch_then (qspecl_then [...]) mp_tac >> simp[] >> strip_tac, then apply helper via drule (REWRITE_RULE[AND_IMP_INTRO] helper) >> simp[].
works_when: Consumer has LIST_REL value_has_type tvs vs + MAP (evaluate_type tenv) ts = MAP SOME tvs and helper needs combined LIST_REL relation
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21246_t001

## L0772 scope='C1.2' tags=evaluate_concat_loop,TypeError,helper_extraction,EVERY
shape: evaluate_concat_loop n (BytesV/BytesV b1) sa ba vs ≠ INR (TypeError msg)
pattern: Extract evaluation loop no-TypeError as a separate helper lemma by induction on the value list. The hypothesis EVERY (λv. ∃bs. v = BytesV bs) vs rules out the TypeError 'concat types' branch. The base and step cases close by rw[evaluate_concat_loop_def] + gvs[] + IH application via drule. Use this helper in concat wrapper proofs via irule + gvs[EVERY_DEF].
works_when: Proving evaluate_builtin concat no-TypeError when all input values are known to have BytesV or StringV kind
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21286_t001

## L0773 scope='C1.2' tags=LIST_REL,LENGTH,induction,length_equality
shape: LIST_REL R l1 l2 implies LENGTH l1 = LENGTH l2
pattern: To prove LENGTH l2 = n from LIST_REL R l1 l2 and LENGTH l1 = n: first derive LENGTH l1 = n via LENGTH_MAP or assumption, then prove LENGTH l2 = LENGTH l1 by Induct_on `l1` >> gvs[LIST_REL_CONS1]. The base case closes by LIST_REL_NIL; the step case closes by LIST_REL_CONS1 decomposing both lists.
works_when: Need to derive list length equality from LIST_REL relation to enable case-splitting on the list
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21389_t001

## L0774 scope='C1.2' tags=Induct,universally_quantified_IH,qspecl_then,drule
shape: Universally-quantified IH from Induct_on cannot be used with drule
pattern: After Induct_on `vs` >> rw[def], the IH has form !vars. P vars ==> Q vars. first_x_assum drule fails because drule matches implications, not universally-quantified facts. Fix: use first_x_assum $ qspecl_then [`arg1`,`arg2`,...] mp_tac >> simp[] to specialize the IH to the exact arguments of the recursive call. The simp[] then closes the resulting goal.
works_when: Applying an induction hypothesis generated by Induct_on where the recursive call changes the accumulator arguments
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21290_t001

## L0775 scope='C1.2' tags=Cases_on,variable_shadowing,rename1,list_destructuring
shape: Cases_on list produces auto-named h/t that may shadow premise variables
pattern: After Cases_on `list_var`, HOL4 auto-names the head 'h' and tail 't'. If a variable named 't' or 'h' already exists in the goal (from theorem premises), subsequent Cases_on `t` resolves the premise variable instead of the list tail. Fix: always use rename1 after list Cases_on to give stable names, e.g. Cases_on `vs` >> rename1 `v1 :: vs2'.
works_when: Case-splitting on a list variable when other short-named variables (t, h, etc.) are in scope from the theorem statement
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21303_t001

## L0776 scope='C1.2' tags=builtin,LIST_REL,value_has_type,evaluate_type,case_simplification
shape: value_has_type <type_var> <value> with LIST_REL + MAP evaluate_type
pattern: When proving builtin no-TypeError/success-type theorems with LIST_REL value_has_type tvs vs and MAP (evaluate_type tenv) ts = MAP SOME tvs: (1) Derive LENGTH vs = n via LIST_REL_LENGTH + LENGTH_MAP. (2) Decompose lists via Cases_on vs >> gvs[LIST_REL_CONS1] (iterate for length n). (3) Resolve TYPE VARIABLES via Cases_on tvs >> gvs[evaluate_type_def, AllCaseEqs()] BEFORE case-splitting any values. (4) Only THEN case-split values - the [local,simp] boundary lemmas (vht_BaseTV_BytesT_Dynamic etc.) will fire once types are concrete. (5) NEVER use gvs[value_has_type_def] - it creates massive case explosions.
works_when: Proving builtin/operator well-typedness theorems where value_has_type assumptions have type variables that need resolving via evaluate_type
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21522_t001
- source:semantics/prop/vyperBuiltinTypingScript.sml:952-962

## L0778 scope='C1.2' tags=evaluate_type_BaseT,BytesT,bytes_bound,eval_type
shape: evaluate_type tenv (BaseT bt) = SOME (BaseTV bt) when IS_SOME
pattern: evaluate_type_BaseT: !tenv bt. IS_SOME (evaluate_type tenv (BaseT bt)) ==> evaluate_type tenv (BaseT bt) = SOME (BaseTV bt). Proof requires Cases_on bt >> rw[evaluate_type_def, LET_THM], then for the BytesT sub-case: Cases_on b (bytes_bound: Fixed/Dynamic) >> gvs[]. The BytesT branch has conditional structure that rw alone doesn't fully decompose. Also need IS_SOME_cond[simp]: IS_SOME(if c then SOME x else NONE) <=> c to help simp handle the conditional IS_SOME goals.
works_when: Need to resolve evaluate_type (BaseT bt) = SOME (BaseTV bt) from IS_SOME assumption. This is stronger than imported evaluate_type_BaseT_cases which only gives ?btv. tv = BaseTV btv.
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21575_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21583_t001

## L0780 scope='C1.2' tags=Slice,reference_proof,builtin_typing,decompose_list_rel
shape: Reference Slice proof pattern from vyperBuiltinTypingScript.sml for success-typing
pattern: Reference proof (line 952-962): gvs[well_typed_builtin_app_def] >> imp_res_tac evaluate_type_BaseT >> gvs[] >> decompose_list_rel_tac >> TRY(Cases_on bd) >> gvs[evaluate_type_def, LET_THM, AllCaseEqs()] >> rename1 evaluate_builtin _ _ _ _ [fv; _; _] >> Cases_on fv >> gvs[value_has_type_def] >> gvs[evaluate_builtin_def, evaluate_slice_def, AllCaseEqs(), LET_THM] >> simp[vht_BytesV_Dynamic, vht_StringV, LENGTH_TAKE]. For no-TypeError, adapt by NOT using AllCaseEqs with evaluate_slice_def, instead resolving dest_NumV first.
works_when: Proving builtin Slice soundness (no-TypeError or success-typing)
evidence:
- source:semantics/prop/vyperBuiltinTypingScript.sml:952-962

## L0781 scope='C1.2' tags=dest_NumV,integer_arithmetic,boundary_lemma,simp_rule
shape: dest_NumV (IntV i) = SOME (Num i) when 0 <= i
pattern: dest_NumV_def has 'if i < 0 then NONE else SOME (Num i)'. Neither gvs nor intLib.ARITH_TAC can close F from 0<=i ∧ i<0 as integer inequalities. Fix: prove boundary lemma !i. 0<=i ==> dest_NumV(IntV i) = SOME(Num i) via `~(i<0:int)` by intLib.ARITH_TAC >> simp[dest_NumV_def]. Mark [local,simp] so it fires automatically. Then any case split on dest_NumV result is resolved by simp without creating NONE branches.
works_when: Any proof where dest_NumV is applied to IntV i with 0<=i assumption from value_has_type UintT
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21708_t001

## L0782 scope='C1.2' tags=evaluate_slice,TypeError,boundary_lemma,abstraction_level
shape: evaluate_slice defined value cannot produce TypeError for well-typed inputs
pattern: evaluate_slice_def contains 'case dest_NumV sv of NONE => INR(TypeError)'. Expanding evaluate_slice_def in a no-TypeError consumer proof creates unresolvable case splits. Fix: Prove a boundary lemma at the implementation level: for BytesV/StringV + IntV(0<=i) inputs, evaluate_slice never returns INR(TypeError). Consumers use irule on this boundary lemma instead of unfolding evaluate_slice_def. The boundary lemma proof can safely Cases_on the value constructors since it's a small focused lemma.
works_when: Proving no-TypeError theorems about functions that call evaluate_slice, where expanding evaluate_slice_def in the consumer proof would create dest_NumV case-split issues
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21746_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21730_t001

## L0783 scope='C1.2' tags=value_has_type,iff_rewrite,Cases_on,existential,gvs_substitution
shape: vht iff lemmas produce existential equations that gvs cannot substitute into goals
pattern: vht_BaseTV_UintT etc. are iff lemmas: value_has_type (BaseTV (UintT n)) v <=> ?i. v = IntV i /\ 0 <= i /\ .... When imp_res_tac adds these, gvs[] applies the rewrite to the assumption but leaves v as a free variable with existential quantifier. gvs does NOT substitute v = IntV i into the goal. Fix: either (1) Cases_on v first then gvs[vht_*] to close impossible cases, or (2) drule vht lemma to get concrete existential witnesses, or (3) prove boundary lemma that takes value_has_type as input and produces the conclusion without needing intermediate variable substitution.
works_when: Using vht iff lemmas to constrain value variables in proofs where the goal contains the variable in a pattern-match position
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21730_t001

## L0786 scope='C1.2' tags=dest_NumV,intLib.ARITH_TAC,if-then-else,integer_comparison
shape: dest_NumV_def if-then-else on i<0 not resolved by fs/simp with 0<=i assumption
pattern: dest_NumV_def has 'if i < 0 then NONE else SOME (Num i)'. Neither fs nor simp resolves this if-then-else using 0 <= i assumption because the integer comparison involves intLib arithmetic that fs can't simplify. Fix: use rw[] which does COND_CASES_TAC internally, or explicitly resolve with `~(i < 0:int)` by intLib.ARITH_TAC before expanding the definition. The [local,simp] lemma dest_NumV_IntV_SOME (!i. 0<=i ==> dest_NumV (IntV i) = SOME (Num i)) handles this provided 0<=i appears BEFORE the definition expansion.
works_when: Expanding definitions containing dest_NumV or similar if-then-else on integer comparisons, where the goal has 0 <= i assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21828_t001

## L0790 scope='C1.2' tags=dest_NumV,intLib.ARITH_TAC,integer_arithmetic,boundary_lemma
shape: dest_NumV(IntV i) = SOME(Num i) when 0 <= i - prove as [local,simp] boundary lemma
pattern: dest_NumV_def has 'if i < 0 then NONE else SOME (Num i)'. Neither gvs nor intLib.ARITH_TAC can close F from 0<=i /\ i<0 as integer inequalities after AllCaseEqs case split. Fix: prove !i. 0<=i ==> dest_NumV(IntV i) = SOME(Num i) via `~(i<0:int)` by intLib.ARITH_TAC >> simp[dest_NumV_def]. Mark [local,simp] so it automatically resolves dest_NumV case splits.
works_when: Any proof where dest_NumV is applied to IntV i with 0<=i assumption from value_has_type UintT
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21708_t001

## L0791 scope='C1.2' tags=gvs,vht,iff,value_has_type,Excl,two_phase
shape: gvs fires [local,simp] vht iff lemmas consuming value_has_type before witness extraction; two-phase approach needed
pattern: When gvs[evaluate_type_def, LET_THM, AllCaseEqs()] resolves evaluate_type to concrete typed_values, the [local,simp] vht iff lemmas (e.g. vht_BaseTV_BytesT_Dynamic) fire on value_has_type assumptions, rewriting them to existential form and often eliminating the fv=Constructor witness WITHOUT substituting into other assumptions. Fix: use gvs[Excl "vht_BaseTV_BytesT_Dynamic", Excl "vht_BaseTV_BytesT_Fixed", Excl "vht_BaseTV_UintT"] to resolve types while preserving value_has_type, then extract witnesses manually via Cases_on + gvs[specific vht lemma]. For proofs with Cases_on bd (Fixed/Dynamic variant), handle each branch with >- syntax separately since Excl prevents closing impossible cases.
works_when: Proving builtin no-TypeError theorems where value_has_type assumptions AND evaluate_builtin/evaluate_slice assumptions reference the same value variables, and gvs would consume the former before the latter can be resolved
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21937_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21940_t001

## L0792 scope='global' tags=edit_lines,Unicode,API,corruption,replace_text
shape: edit_lines corrupts Unicode characters in HOL4 SML files; use replace_text with Unicode input instead
pattern: NEVER use edit_lines for HOL4 SML files. edit_lines converts ∧ to /&#39;, ∨ to similar entities, ≠ to &lt;&gt;, >> to &gt;&gt;, etc. replace_text and write_file correctly preserve Unicode characters ∧ ∨ ≠ ∀ ∃ ≤ ≥ when provided as Unicode input. For targeted small edits, use replace_text matching exact existing text (without line numbers).
works_when: Any edit to HOL4 SML files containing Unicode mathematical symbols
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21884_t001

## L0793 scope='C1.2' tags=vht,wrapper_lemma,witness_extraction,boundary_lemma,evaluate_slice
shape: Add vht-level wrapper lemma that takes value_has_type directly to isolate witness extraction
pattern: When consumer proofs can't extract witnesses because gvs/expansion ordering issues prevent matching vht iff lemmas, add a vht-level wrapper lemma that takes value_has_type assumptions directly and proves the no-TypeError conclusion. The wrapper lemma's proof can safely Cases_on the value variable and use gvs[specific vht iff lemma] because it's an isolated focused lemma. Consumer proofs then apply irule on the wrapper lemma. For BytesT Slice, need two wrappers: one for Fixed and one for Dynamic bytes.
works_when: Consumer proofs have complex type resolution that interferes with witness extraction from value_has_type assumptions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21937_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21942_t001

## L0794 scope='C1.2' tags=gvs,negation,irule,noteq,F_goal,metis_tac
shape: gvs transforms ≠ goal into F with equality assumption; irule fails on F goal
pattern: When a goal is 'x ≠ INR(TypeError msg)' (aka ¬(x = INR(TypeError msg))), gvs may convert it to goal F with assumption 'x = INR(TypeError msg)'. After this transformation, irule cannot match a lemma conclusion 'x ≠ INR(TypeError msg)' against goal F. Fix: use metis_tac[boundary_lemma] which derives F from the contradictory combination of the boundary lemma + the equality assumption + the bound assumptions. Alternative: use simp instead of gvs to preserve the ≠ goal form, then irule works.
works_when: Proving no-TypeError wrapper lemmas where gvs simplifies the negation goal to F with equality assumption, and a boundary lemma provides the ≠ conclusion
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21978_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21992_t001

## L0795 scope='C1.2' tags=wrapper_lemma,value_has_type,evaluate_slice,boundary_abstraction
shape: Wrapper lemma taking value_has_type assumptions isolates witness extraction from consumer proofs
pattern: For consumer proofs that need to relate value_has_type assumptions to evaluate_builtin/evaluate_slice calls, prove a wrapper lemma that takes value_has_type directly and proves the no-TypeError/success-typing conclusion. The wrapper handles the Fixed/Dynamic bytes_bound case split and value constructor witness extraction internally. Consumer proofs just irule/metis_tac the wrapper after deriving value_has_type. This avoids gvs/consumer proof interference where vht iff lemmas fire unexpectedly.
works_when: Consumer proofs have value_has_type assumptions that need to be connected to evaluate_builtin/evaluate_slice without expanding internal definitions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m21978_t001

## L0796 scope='C1.2' tags=imp_res_tac,evaluate_type_BaseT,StringT,proof_pattern
shape: imp_res_tac evaluate_type_BaseT >> gvs[] then simp[evaluate_builtin_def] pattern for builtin no-TypeError
pattern: For builtin no-TypeError theorems where evaluate_type returns BaseTV: use imp_res_tac evaluate_type_BaseT >> gvs[] to resolve type variables, then simp[evaluate_builtin_def] to expand the builtin call. Do NOT use Cases_on bytes_bound BEFORE simp - the Fixed/Dynamic split should happen inside a wrapper lemma, not in the consumer.
works_when: Proving builtin no-TypeError theorems after list decomposition (Cases_on vs/ts)
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1438-1460

## L0797 scope='C1' tags=Excl,vht_BaseTV,iff,simp,fs,gvs,value_has_type,boundary_lemma
shape: [local,simp] iff lemmas consuming value_has_type assumptions needed as boundary lemma premises
pattern: When value_has_type (BaseTV (UintT n)) v (and similar) assumptions are needed as premises for a boundary lemma (e.g. evaluate_slice_BytesT_no_type_error), use Excl "vht_BaseTV_UintT" (and Excl for BytesT iff lemmas) in fs/gvs calls between type-variable resolution and boundary lemma application. Without Excl, fs/gvs decompose these assumptions into sv=IntV i + bounds, making them match neither the boundary lemma premises nor reconstructible via metis (2**n vs literal gap blocks FOL).
works_when: A boundary lemma requires value_has_type premises but intermediate fs/gvs steps would decompose those premises via [local,simp] iff rules
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22074_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22076_t001

## L0798 scope='C1' tags=evaluate_type_BaseT_SOME,type_variable,resolution
shape: Resolving abstract type variables from evaluate_type = SOME x assumptions
pattern: Add a lemma evaluate_type_BaseT_SOME: !tenv bt tv. evaluate_type tenv (BaseT bt) = SOME tv ==> tv = BaseTV bt. This directly resolves x = BaseTV (BytesT bd) etc from evaluate_type (get_tenv cx) (BaseT bt) = SOME x assumptions. Better than evaluate_type_BaseT which needs IS_SOME. Use imp_res_tac evaluate_type_BaseT_SOME >> fs[Excl ...] to substitute type variables while preserving other value_has_type assumptions.
works_when: After LIST_REL value_has_type + MAP (evaluate_type tenv) ts = MAP SOME tvs, the tvs variables are abstract and need resolution to concrete BaseTV/ArrayTV/TupleTV form
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22074_t001

## L0811 scope='C4.2' tags=ecrecover,list_destruct,EL-index,simp
shape: Proving ecrecover_no_type_error without gvs list destruct
pattern: For ecrecover_no_type_error (4-element list), use either: (1) EL-index approach: witness EL 0/1/2/3 vs, use LIST_REL_EL_EQN + EVERY_EL + EL_MAP to connect typing predicates, then irule boundary lemma; or (2) simp-based element destruct matching vyperBuiltinTypingScript.sml pattern (Cases_on vs >> simp then Cases_on h >> simp ...). Do NOT use gvs[LIST_REL_CONS1] as it produces unpredictable tail names. All needed boundary lemmas are already proved at lines 1511-1539.
works_when: Proving ECRecover or similar builtins with fixed-arity argument lists that need list destruct
evidence:
- episode:E0160
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22429_t002

## L0812 scope='global' tags=Unicode,API,write_corruption,workaround
shape: API corrupts Unicode logical connectives in Theorem statements
pattern: The API corrupts Unicode conjunction and disjunction when writing NEW Theorem statements. Workaround: (1) only edit EXISTING theorem text where Unicode is already on disk; (2) for proof bodies, Unicode in backtick term quotations appears to survive; (3) if new lemma statements are truly needed, use HOL4 ASCII alternatives /\ and \/ which the API handles correctly. Always grep for /¥ after writing to detect corruption.
works_when: Any situation requiring new HOL4 theorem statements with Unicode logical connectives through the API
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22459_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22492_t001

## L0817 scope='C4.2' tags=ecrecover,EL-index,EL_MAP,fs-failure,metis
shape: Deriving evaluate_type (EL i ts) = SOME (EL i tvs) from MAP equality plus EL_MAP
pattern: When deriving per-element facts from MAP equalities using EL_MAP: do NOT use fs[] to bridge the transitivity chain (EL(MAP f ts) = f(EL i ts)), (EL(MAP g tvs) = g(EL i tvs)), and (MAP f ts = MAP g tvs). Instead use metis_tac[EL_MAP] which handles the transitive chain. The two intermediate `by simp[EL_MAP]` steps produce assumptions that metis_tac can connect via the MAP equality.
works_when: Proving element-wise evaluation type equalities from MAP evaluate_type ts = MAP SOME tvs with known list lengths
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22526_t002

## L0818 scope='C4.2' tags=vht,BytesT,value_destruct,simp
shape: vht_BaseTV_BytesT_Fixed requires concrete BytesV constructor, not variable
pattern: The [local,simp] lemma vht_BaseTV_BytesT_Fixed (value_has_type (BaseTV(BytesT(Fixed 32))) (BytesV bs) <=> LENGTH bs = 32) only fires in simp when the value argument IS a BytesV constructor. For a variable v0 with value_has_type (BaseTV(BytesT(Fixed 32))) v0, must Cases_on `v0` first, then fs[vht_BaseTV_BytesT_Fixed] in the BytesV branch. Other vht lemmas (vht_BaseTV_UintT etc.) have the same pattern.
works_when: Using vht_BaseTV_* lemmas to decompose value_has_type when the value is a universally quantified variable, not a concrete constructor
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:191
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1637

## L0820 scope='C4.2' tags=EL_MAP,metis,MAP_equality
shape: Deriving evaluate_type(EL i ts) = SOME(EL i tvs) from MAP equality
pattern: From MAP (evaluate_type tenv) ts = MAP SOME tvs with LENGTH ts = n, derive: !i. i < n ==> evaluate_type tenv (EL i ts) = SOME (EL i tvs). Use metis_tac[EL_MAP] which handles full transitivity chain. Do NOT use fs[] - it cannot bridge two EL_MAP results plus MAP equality.
works_when: Deriving element-wise evaluation type equalities from MAP equalities with known list lengths
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22600_t001

## L0823 scope='C4.2' tags=res_tac,EL_index,metis_tac,quantified_facts
shape: Specializing quantified EL-index list facts to concrete indices and type arguments
pattern: When you have !i. i < n ==> value_has_type (EL i tvs) (EL i vs) but need value_has_type (BaseTV (BytesT (Fixed 32))) (EL 0 vs): res_tac CANNOT bridge the gap because the type argument mismatch (EL i tvs vs BaseTV(BytesT(Fixed 32))) requires substitution via a separately proved EL 0 tvs = BaseTV(BytesT(Fixed 32)) fact. Instead: use `value_has_type (EL 0 tvs) (EL 0 vs)` by metis_tac[] (instantiates i=0), then metis_tac[] with the EL 0 tvs = BaseTV(...) fact to do the type substitution. For converter non-NONE: same pattern, derive value_has_type (EL i tvs) (EL i vs) first, then compose with type disjunction.
works_when: Proving properties from quantified list-rel EL-index facts where the desired type argument differs from the EL-index form
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22640_t002

## L0824 scope='C4.2' tags=Unicode,API_corruption,disjunction,Theorem_statement
shape: Avoiding Unicode disjunction in new Theorem statements written through API
pattern: When adding new Theorem statements through the API that need logical disjunction: use ASCII \/ instead of Unicode ∨, /\ instead of ∧, ! instead of ∀, ? instead of ∃, \t. instead of λt.. The API corrupts Unicode logical connectives (L0812). As an alternative, reformulate to avoid disjunction entirely: e.g., use ecrecover_arg_to_num v <> NONE (derived property) instead of value_has_type (BaseTV(UintT 256)) v \/ value_has_type (BaseTV(BytesT(Fixed 32))) v (structural disjunction).
works_when: Writing new Theorem statements in HOL4 SML files through the replace_text/write_file API
evidence:
- source:semantics/prop/LEARNINGS_type_system_rewrite.md L0812

## L0825 scope='C4.2' tags=list_el_decomp,EL,list_decomposition,fixed_length
shape: Proving l = [EL 0 l; EL 1 l; ...; EL (n-1) l] from LENGTH l = n
pattern: For fixed-length list decomposition (n=2,3,4), prove a local helper list_el_decomp_n: !l. LENGTH l = n => l = [EL 0 l; ..., EL (n-1) l]. Proof: iterated Cases_on >> fs[] >> simp[EL]. Use: simp[list_el_decomp_4] with assumption LENGTH vs = 4 closes existential ?v0 v1 v2 v3. vs = [v0;v1;v2;v3] in one step with witnesses EL 0..3 vs. Do NOT use match_mp_tac LIST_EQ >> simp[] (universal EL subgoal unsolved by simp) or LIST_EQ_EL_EQN (nonexistent).
works_when: Decomposing a list of known finite length into named elements for builtin argument lists of fixed arity
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22670_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22642_t002

## L0827 scope='C4.2' tags=extract_ec_point,boundary_lemma,ArrayTV,uint256,ecadd,ecmul
shape: extract_ec_point succeeds on typed uint256[2] array values
pattern: For ECAdd/ECMul no-TypeError proofs: prove extract_ec_point_uint256_2_not_none boundary lemma (!av. value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (ArrayV av) ==> extract_ec_point (ArrayV av) != NONE). Then in consumer: derive value_has_type via EL-index, do Cases_on 'EL i vs' >> metis_tac[extract_ec_point_uint256_2_not_none], then fs[evaluate_builtin_def, evaluate_ecadd/ecmul_def, extract_ec_point_def, AllCaseEqs()].
works_when: Proving ECAdd/ECMul no-TypeError where both args are uint256[2] arrays and extract_ec_point must succeed
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m22730_t001

## L0861 scope='C4' tags=no-TypeError,group-lemma,Cases_on-type-value,simp-not-fs,vht-rules
shape: Resolving type→value constructors in no-TypeError proofs: Cases_on type_value + simp[vht_*] not Cases_on type + fs[]
pattern: When you need to go from evaluate_type tenv ty = SOME tv and value_has_type tv v to concrete value constructors (v = IntV i etc.), do: (1) Cases_on `tv` to get BaseTV/FlagTV/etc constructors, (2) simp[vht_BaseTV_UintT, vht_BaseTV_IntT, ...] to resolve value constructors. Do NOT use Cases_on `ty` + fs[is_int_type_def] because the catch-all simp rules on free variables destroy the proof. The vht_* rules are safe because they match on the known type_value constructor.
works_when: Any proof that needs value constructor resolution from type typing assumptions, especially in no-TypeError theorems with !msg conclusions
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:155-207
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23369_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23313_t001

## L0862 scope='C4' tags=
shape: Type classifier [simp] defs with catch-all _ = F block expansion in no-TypeError proofs: use Excl to remove them
pattern: When is_int_type_def, is_numeric_type_def, is_bool_type_def, is_flag_type_def, is_comparable_type_def, is_bytes_or_string_type_def are all in the [simp] set with catch-all _ = F rules, and you need to expand well_typed_binop_def or similar assumptions that produce type classifier predicates: use simp[well_typed_binop_def, Excl "is_int_type_def", Excl "is_numeric_type_def", Excl "is_bool_type_def", Excl "is_flag_type_def", Excl "is_comparable_type_def", Excl "is_bytes_or_string_type_def", is_int_type_inv, is_numeric_type_inv, is_bool_type_inv, is_flag_type_inv, is_comparable_type_inv]. The Excl directive removes the catch-all from the simpset for this call; the inversion lemmas provide safe catch-all-free expansions. If Excl doesn't work, use pure REWRITE_RULE[well_typed_binop_def] which doesn't use the simpset.
works_when: Proving well_typed_binop_no_type_error or any no-TypeError dispatcher theorem where expanding a definition creates type classifier predicates with free variables that trigger catch-all [simp] rules
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:20-24
- source:semantics/prop/vyperTypeBuiltinsScript.sml:223-254
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23389_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23369_t002
- episode:E0164

## L0863 scope='C4' tags=
shape: Expand an assumption in the goal instead of using fs[]: qpat_x_assum mp_tac >> simp[safe_lemmas] >> strip_tac
pattern: To expand a definition-assumption (like well_typed_binop_def) in a no-TypeError theorem without triggering catch-all [simp] rules on other assumptions: (1) qpat_x_assum `assumption_pattern` mp_tac to push it to the goal as antecedent, (2) simp[definition, inversion_lemmas, Excl ...] to expand only the goal, (3) strip_tac to bring expanded form back as assumptions. This avoids fs[]/gvs[] which would simplify all assumptions and could trigger catch-all rewrites. For value resolution, similarly: qpat_x_assum `value_has_type _ v1` mp_tac >> simp[vht_BaseTV_UintT] >> strip_tac.
works_when: Any no-TypeError proof where expanding a definition in assumptions with fs[]/gvs[] causes catch-all rules to fire on other assumptions or the conclusion
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23369_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23389_t002
- source:semantics/prop/vyperTypeBuiltinsScript.sml:155-207

## L0864 scope='global' tags=
shape: Theorem with !msg. f <> INR(TypeError msg) conclusion: avoid fs[] and gvs[] entirely; use simp[] + mp_tac or REWRITE_RULE
pattern: When proving theorems of the form !msg. f x <> INR(TypeError msg), NEVER use fs[] or gvs[]. Three failure modes: (1) fs[] can rewrite the disequation using type-classifier equalities derived from assumptions, producing F; (2) gvs[] eliminates the !msg variable, producing an unsolvable concrete disequation; (3) both fire catch-all [simp] rules like is_int_type _ = F on free type variables. Safe alternatives: simp[] (changes conclusion only), qpat_x_assum mp_tac >> simp[] >> strip_tac, or pure REWRITE_RULE.
works_when: Any no-TypeError theorem with universally-quantified msg in a disequation conclusion, especially with type classifier assumptions on free variables
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23247_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23345_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23369_t002

## L0865 scope='C4.1' tags=definition_fix,constructor_names,well_typed_binop,UnsafeAdd,binop_datatype
shape: well_typed_binop_def Unsafe* constructor names must match binop Datatype
pattern: well_typed_binop_def in vyperTypeSystemScript.sml uses UnsafeAdd/UnsafeSub/UnsafeMul/UnsafeDiv (FIXED). The binop Datatype (vyperAST) also uses UnsafeAdd/UnsafeSub/UnsafeMul/UnsafeDiv. These MUST match for Cases_on bop to work. This was already fixed in the current source.
works_when: Any proof involving well_typed_binop_def after Cases_on bop - verified the fix builds clean
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:93-96
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23469_t001

## L0866 scope='C4.1' tags=type_classifier,catch_all,simp_rule,is_int_type,inversion_lemma,REWRITE_TAC
shape: Type classifier catch-all [simp] rules vs safe inversion lemmas
pattern: Type classifiers like is_int_type_def, is_numeric_type_def, is_bool_type_def etc have [simp] catch-all rules (e.g., is_int_type _ = F) that fire incorrectly on free type variables, destroying proof state. NEVER use fs/gvs/simp with these defs when type vars could be free. Instead use inversion lemmas (is_int_type_inv, is_numeric_type_inv, is_bool_type_inv, is_flag_type_inv, is_comparable_type_inv, is_bytes_or_string_type_inv) which are safe iff lemmas WITHOUT catch-alls. Use pattern: qpat_x_assum `is_int_type _` mp_tac >> REWRITE_TAC[is_int_type_inv] >> strip_tac. This pushes classifier to goal antecedent, rewrites with safe iff, and strips disjunction. Alternatively, after Cases_on on the type variable (making vars concrete), simp[is_int_type_def] IS safe.
works_when: Any proof where type classifiers appear as assumptions with free type variables - which is the standard situation after PURE_ONCE_REWRITE_TAC[well_typed_binop_def] >> strip_tac
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:223-263
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23389_t002
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23474_t001

## L0872 scope='C4' tags=value-resolution,mp_tac,vht,no-TypeError,evaluate_binop
shape: Resolving runtime value constructors from value_has_type after type resolution: mp_tac >> simp >> strip_tac >> simp
pattern: When type-level bindings are established (tv1 = BaseTV (UintT n), tv2 = BaseTV (UintT n)) but values v1/v2 are still free, resolve them with: qpat_x_assum `value_has_type _ v1` mp_tac >> simp[] >> strip_tac >> simp[] (vht_* rules are [local,simp] so simp[] suffices for UintT/IntT/BoolT). For DecimalT use simp[vht_BaseTV_DecimalT] explicitly. This gives v1 = IntV i with bounds or v = DecimalV d. Then irule the per-operator boundary lemma.
works_when: Proving evaluate_binop no-TypeError theorems after type resolution is done and value_has_type assumptions still contain free value variables
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:846-937
- source:semantics/prop/vyperTypeBuiltinsScript.sml:155-207

## L0873 scope='C4.1' tags=binop,no-TypeError,inline-resolution,dispatcher-proof,is_int_type_imp,evaluate_type_BaseT_SOME,ACCEPT_TAC,MATCH_MP,mp_tac,vht
shape: well_typed_binop_no_type_error or similar dispatcher: inline type+value resolution per case
pattern: For no-TypeError dispatcher theorems where type classifier expansion is needed: do NOT use helper lemmas with drule_all. Instead inline the resolution per case: (1) derive type disjunction with `is_int_type ty ∨ ty = BaseT DecimalT` by metis_tac[is_numeric_type_inv], (2) split with `>-`, (3) derive ∃-disjunction with `(∃n. ty = BaseT (UintT n)) ∨ (∃n. ty = BaseT (IntT n))` by (first_x_assum (fn th => ACCEPT_TAC (MATCH_MP is_int_type_imp th))), (4) specialize with first_x_assum (qspec_then `n` strip_assume_tac), (5) resolve type_values with `result_tv = BaseTV (UintT n)` by metis_tac[evaluate_type_BaseT_SOME], (6) resolve values with qpat_x_assum `value_has_type _ v1` mp_tac >> simp[] >> strip_tac >> simp[], (7) irule per-operator boundary lemma. This pattern is repeatable and avoids variable scoping bugs.
works_when: Any multi-case dispatcher theorem where well_typed_binop_def expansion produces type classifier predicates and goal has value variables matching helper ∃-quantified variables
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23716_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:740-1461

## L0874 scope='C4' tags=qspec_then,strip_assume_tac,existential,universal,variable-resolution,wrong-tactic
shape: Resolving ∃-quantified assumptions from disjunction splits: use strip_assume_tac NOT qspec_then
pattern: When a disjunction split produces an assumption of form ∃n. P n (e.g., from is_int_type_imp), do NOT use first_x_assum (qspec_then `n` strip_assume_tac). qspec_then specializes ∀-quantified theorems only. Instead use: first_x_assum strip_assume_tac (auto-names the witness), or first_x_assum (qx_choose_then `n` strip_assume_tac) (explicitly names it). After strip_assume_tac, the witness variable gets an auto-generated name (possibly primed); metis_tac[evaluate_type_BaseT_SOME] can chain through the resulting equality to derive type_value bindings. Use rename1 `n` only if the auto-name causes later matching issues.
works_when: Any proof that derives existential assumptions from disjunction splits (e.g., from is_int_type_imp, is_flag_type_imp, is_comparable_type_imp) and needs to extract the witness variable
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23801_t001

## L0875 scope='C4.1' tags=binop,dispatcher-proof,per-case-parentheses,>-,disjunction,Cases_on,well_typed_binop
shape: well_typed_binop_no_type_error: wrap each Cases_on bop case in parenthesized block
pattern: For well_typed_binop_no_type_error, after Cases_on bop creates 22 subgoals, each case must be handled in its own parenthesized block (>- (...) not >> tac). Inside each block: (1) qpat_x_assum well_typed_binop mp_tac, (2) PURE_ONCE_REWRITE_TAC[well_typed_binop_def], (3) rpt strip_tac, (4) handle type/value resolution with strip_assume_tac for ∃ goals, (5) irule boundary lemma. This prevents disjunction splits in And/Or/XOr/In/NotIn from contaminating the >- structure.
works_when: Proving well_typed_binop_no_type_error or any multi-case dispatcher theorem where some cases produce disjunction splits within their well_typed_* definition
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23801_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23734_t001

## L0876 scope='C4.1' tags=existential,qspec_then,qx_choose_then,by,STRIP_ASSUME_TAC,Cases_on,well_typed_binop
shape: Type classifier disjunction with existential witnesses under `by` subgoals
pattern: NEVER use `by` with disjunctions containing ∃-quantified witnesses when you need to name the witnesses later. STRIP_ASSUME_TAC (used by `by`) destructs ∃ silently, consuming the assumption. Instead, use Cases_on the type variable directly (e.g., Cases_on `ty` >> gvs[is_int_type_def]) which gives stable named constructors. gvs[is_int_type_def, is_numeric_type_def] is safe AFTER Cases_on because catch-all simp rules (is_int_type _ = F) correctly evaluate on concrete constructors.
works_when: Proving theorems about type classifiers where well_typed_binop_def or similar definitions contain is_int_type ty / is_numeric_type ty / is_bool_type ty as disjunctive conditions
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23832_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23801_t001

## L0878 scope='C4' tags=
shape: After Cases_on a datatype with inner types (like type with BaseT base_type), the inner variable is free, making gvs with catch-all [simp] classifier defs unsafe
pattern: After Cases_on `ty` where `type = BaseT base_type | TupleT | ...`, the BaseT case has a free base_type variable (auto-named). gvs[is_int_type_def, etc] fires catch-all `_ = F` rules on this free variable, killing valid subcases. CORRECT: handle BaseT first with `>- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[...])`, making base_type concrete BEFORE gvs. Non-BaseT cases handled separately by `>> gvs[...]`.
works_when: Any proof using Cases_on on vyper_type (or similar datatype with inner type arguments) followed by gvs/fs with type classifier definitions
evidence:
- episode:E0164
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23854_t001

## L0879 scope='C4' tags=
shape: Use Cases_on `result_tv` (type_value) instead of Cases_on `ty` (type) for type+value resolution in binop soundness
pattern: When going from evaluate_type tenv ty = SOME result_tv and well_typed_binop conditions to concrete value constructors, Cases_on `result_tv` is MORE ROBUST than Cases_on `ty` because: (1) result_tv directly gives type_value constructors (BaseTV/FlagTV/etc), (2) After Cases_on `result_tv`, vht_* [local,simp] rules directly resolve value constructors without needing a separate type-to-type_value-to-value chain, (3) No free-inner-variable catch-all issue on BaseTV because vht_* rules match on the type_value argument. Combine with Cases_on `tv1`/`tv2` for operand type_values.
works_when: Proving evaluate_binop no-TypeError theorems where evaluate_type equations constrain type_values and well_typed_binop conditions constrain the type structure
evidence:
- source:semantics/prop/vyperTypeBuiltinsScript.sml:155-207
- source:semantics/prop/vyperTypeBuiltinsScript.sml:642-665

## L0880 scope='C4.1' tags=well_typed_binop,no-TypeError,RULE_ASSUM_TAC,DISJ_CASES_TAC,type_classifier,is_int_type_inv,is_numeric_type_inv
shape: well_typed_binop_no_type_error: type resolution via RULE_ASSUM_TAC + DISJ_CASES_TAC instead of Cases_on
pattern: For no-TypeError dispatcher proofs with type classifier predicates (is_numeric_type ty, is_int_type ty etc.): do NOT use Cases_on for type resolution. Instead: (1) push well_typed_binop def to goal via mp_tac >> PURE_ONCE_REWRITE_TAC[well_typed_binop_def] >> rpt strip_tac, (2) RULE_ASSUM_TAC(REWRITE_RULE[is_numeric_type_inv, is_int_type_inv, is_bool_type_inv, is_flag_type_inv, is_comparable_type_inv]) to convert classifier assumptions to concrete disjunctions, (3) first_x_assum DISJ_CASES_TAC to split the disjunctions into separate subgoals, (4) strip_assume_tac for existential witnesses from disjunction splits, (5) evaluate_type_BaseT_SOME for type_value resolution, (6) mp_tac + simp + strip_tac + simp for value resolution using vht_* rules, (7) irule per-operator boundary lemma. This avoids the Cases_on free-variable catch-all bug entirely.
works_when: Any no-TypeError dispatcher theorem where expanding a definition creates type classifier predicates with catch-all [simp] rules that fire on free variables
evidence:
- episode:E0164
- episode:E0169
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23901_t002
- source:semantics/prop/vyperTypeBuiltinsScript.sml:223-281

## L0881 scope='C4' tags=Cases_on,free_variable,catch_all,type_classifier,gvs_unsafe,base_type
shape: Cases_on on datatype with inner type args + gvs with catch-all [simp] classifier defs is UNSAFE when inner variable is free
pattern: After Cases_on on a datatype like `type = BaseT base_type | TupleT | ...`, the BaseT case has a FREE inner variable (auto-named bv/v/b' etc.). NEVER use gvs/fs/simp with type classifier defs (is_int_type_def, is_numeric_type_def etc.) while this inner variable is free, because catch-all rules like `is_int_type _ = F` fire on `is_int_type (BaseT bv)` deriving F and killing valid subcases. CORRECT approaches: (1) Cases_on the inner variable FIRST making it concrete: `rename1 `BaseT bt` >> Cases_on `bt` >> gvs[...]`, or (2) avoid Cases_on entirely and use RULE_ASSUM_TAC(REWRITE_RULE[is_*_type_inv]) + DISJ_CASES_TAC for type resolution, or (3) Excl the catch-all defs from the simpset.
works_when: Any proof using Cases_on on vyper_type or similar datatype with inner type arguments, followed by simplification with type classifier definitions
evidence:
- episode:E0164
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23854_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23901_t002

## L0882 scope='C4.1' tags=gvs,Excl,type_classifier,inversion_lemma,catch_all,well_typed_binop
shape: gvs[well_typed_binop_def, Excl is_*_type_def, is_*_type_inv, AllCaseEqs()] after Cases_on binop
pattern: Use gvs[Excl is_int_type_def, Excl is_numeric_type_def, Excl is_bool_type_def, Excl is_flag_type_def, Excl is_comparable_type_def, is_int_type_inv, is_numeric_type_inv, is_bool_type_inv, is_flag_type_inv, is_comparable_type_inv, AllCaseEqs()] to resolve type classifiers without catch-all _=F rules firing on free variables. The Excl prevents bad simp rules; the _inv lemmas provide good disjunction rewrites. After gvs, irule per-operator boundary lemmas closes most goals. For Div/Mod/Exp: simp[Once evaluate_binop_def] >> rpt IF_CASES_TAC >> simp[]. For In/NotIn array: drule vht_ArrayTV_exists >> strip_tac >> gvs[].
works_when: Type classifier assumptions with free inner variables. Same approach already proved working in well_typed_binop_success_type companion theorem.
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23982_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23997_t001

## L0883 scope='global' tags=edit_lines,replace_text,surgical_edit,helper_lemma
shape: Replacing a Theorem proof body without deleting adjacent helper lemmas
pattern: Use replace_text on the exact Proof..QED text rather than edit_lines on a line range. edit_lines on a wide range can accidentally delete [local] helper Theorem definitions between the target theorem and the next theorem. If you must use edit_lines, first verify the exact range contains only the target theorem and its comment, not any helper lemmas.
works_when: Replacing a proof body in a file that also contains helper lemmas between theorems
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23985_t001

## L0884 scope='C4.1' tags=∀msg,no-TypeError,gen_tac,irule,boundary-lemma
shape: Proving ∀msg. f ≠ INR(TypeError msg): gen_tac first, then irule with boundary lemmas
pattern: For no-TypeError theorems with conclusion ∀msg. evaluate_binop u tv bop v1 v2 ≠ INR (TypeError msg): after gvs resolves type/value constructors, use gen_tac to strip ∀msg, then irule per-operator boundary lemmas (binop_no_type_error_Add etc.) for simple cases. For Div/Mod/Exp with conditionals: simp[Once evaluate_binop_def] >> rpt IF_CASES_TAC >> simp[]. For comparison operators: simp[Once evaluate_binop_def] >> Cases_on v1/v2 >> gvs[value_has_type_def].
works_when: No-TypeError dispatcher theorems where evaluate_binop returns INL or INR(RuntimeError) for well-typed inputs, and ∀msg quantifier blocks direct gvs/simp simplification
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24094_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23982_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:284-618
- source:semantics/prop/vyperTypeBuiltinsScript.sml:1007-1086

## L0885 scope='C4' tags=gvs,Excl,type_classifier,catch_all,well_typed_binop,value_has_type_def
shape: gvs[well_typed_binop_def, Excl is_*_type_def, is_*_type_inv, AllCaseEqs()] resolves type classifiers without catch-all _=F rules
pattern: When expanding well_typed_binop_def or similar definitions that produce type classifier predicates (is_int_type, is_numeric_type, etc.) with free variables: use gvs[well_typed_binop_def, Excl "is_int_type_def", Excl "is_numeric_type_def", Excl "is_bool_type_def", Excl "is_flag_type_def", Excl "is_comparable_type_def", is_int_type_inv, is_numeric_type_inv, is_bool_type_inv, is_flag_type_inv, is_comparable_type_inv, evaluate_type_def, AllCaseEqs()] to resolve type classifiers without catch-all _=F rules firing on free variables. The Excl prevents bad simp rules; the _inv lemmas provide safe disjunction rewrites. After gvs, all 56 goals have concrete type_value and value constructors.
works_when: Any proof where expanding a definition creates type classifier predicates with catch-all [simp] rules that fire on free variables
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24094_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23982_t001

## L0886 scope='global' tags=holbuild,checkpoint,git-stash,file-restore
shape: Restoring accidentally deleted helper lemmas between theorems: use git stash not edit_lines
pattern: When edit_lines or wide replace_text accidentally deletes helper lemmas between theorems: 1) git stash to save broken edits, 2) git checkout to restore the file (if allowed, else git stash pop then manually fix). For surgical proof replacement, use replace_text matching only the Proof..QED body of ONE theorem, not edit_lines on a wide range that covers adjacent helper lemmas.
works_when: Any situation where a wide edit accidentally removed content between theorems
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23985_t001

## L0887 scope='C4.1' tags=gvs,well_typed_binop,In,NotIn,NotEq,impossible_cases,existential
shape: gvs[well_typed_binop_def, Excl is_*_type_def, AllCaseEqs()] leaves impossible In/NotIn/NotEq-int goals
pattern: When gvs processes In/NotIn/NotEq cases in well_typed_binop_no_type_error, it can't fully derive contradiction from the disjunction+existential constraint ((?fid. t1=FlagT fid /\ t2=FlagT fid) \/ (?bd. t2=ArrayT t1 bd)) combined with concrete types from evaluate_type. ~4 impossible In/NotIn/NotEq-int goals survive. After gen_tac, simp[evaluate_binop_def] reduces these to unsolvable 'binop'!=msg. Fix: derive F from remaining assumptions or add helper lemma well_typed_binop_In_not_int_type. Alternative: irule per-operator boundary lemmas without expanding well_typed_binop_def.
works_when: Proving well_typed_binop_no_type_error or similar no-TypeError theorems where In/NotIn/NotEq have existential+disjunction type constraints
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24171_t001
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24144_t001

## L0888 scope='C4.1' tags=forall-msg,gen_tac,gvs,conclusion_quantifier
shape: forall-msg in conclusion prevents gvs from fully simplifying
pattern: When conclusion has !msg. P != INR(TypeError msg), gvs can't simplify under the quantifier. Must gen_tac AFTER gvs to strip it. Companion theorem well_typed_binop_success_type with value_has_type result_tv v conclusion works directly with gvs because conclusion simplification feeds back to eliminate impossible cases. For != conclusions, gvs can't get this feedback.
works_when: No-TypeError theorems with !msg. P != INR(TypeError msg) conclusion
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24171_t001

## L0889 scope='C4.1' tags=binop_no_type_error,per-operator,boundary_lemma,irule
shape: Per-operator binop_no_type_error boundary lemmas close most goals after gvs+gen_tac
pattern: After gvs resolves types+values and gen_tac strips !msg, most ~56 goals match per-operator boundary lemmas: binop_no_type_error_Add (simp[evaluate_binop_def]), binop_no_type_error_Div (simp + COND_CASES_TAC), binop_no_type_error_Eq_int (simp + Cases_on v1/v2), etc. NotIn/NotEq with flag types: simp[Once evaluate_binop_def, binop_negate_def]. Comparison: simp[Once evaluate_binop_def] then Cases_on v1/v2 + gvs[value_has_type_def].
works_when: Resolving individual binop no-TypeError goals after gvs has resolved type constructors
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24144_t001
- source:semantics/prop/vyperTypeBuiltinsScript.sml:284-500

## L0890 scope='C4.1' tags=gvs,Excl,type_classifier,irule,binop
shape: gvs[well_typed_binop_def, Excl is_*_type_def, is_*_type_inv, AllCaseEqs(), evaluate_type_BaseT_SOME] + irule per-operator boundary lemmas
pattern: For well_typed_binop_no_type_error: use gvs with Excl on all is_*_type_def catch-all rules (they fire incorrectly on free variables), plus is_*_type_inv to replace classifiers with concrete disjunctions, plus evaluate_type_BaseT_SOME (not evaluate_type_def) to keep FlagT/StructT/NoneT cases manageable. After gvs, route to per-operator boundary lemmas via irule (e.g. irule binop_no_type_error_Add). Div/Mod/Exp need additional rpt IF_CASES_TAC >> simp[]. In/NotIn need drule vht_ArrayTV_exists >> strip_tac >> gvs[]. NotIn/NotEq also close via simp[Once evaluate_binop_def, binop_negate_def].
works_when: Proving no-TypeError properties over evaluate_binop where well_typed_binop_def has type classifiers and disjunctions that gvs must resolve without consuming needed contradictions
evidence:
- episode:E0170
- tool_output:TO_type_system_rewrite-20260516T153850Z_m23982_t001

## L0891 scope='C4.1' tags=git,restore,file_corruption
shape: Broken proof file with missing QED or truncated Proof body
pattern: If a Proof..QED block gets corrupted (missing QED, leftover FAIL_TAC probe, deleted helper lemmas), restore the file via git checkout BEFORE attempting any further edits. Never try to patch incrementally from a broken state.
works_when: Any time git diff shows unexpected deletions or malformed proof blocks
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24250_t001

## L0892 scope='global' tags=definition_mismatch,constructor_names,Cases_on,unprovable
shape: msg ≠ string_literal goal after Cases_on + gvs with definition expansion
pattern: CRITICAL: Before any case-split proof over an algebraic type, grep both the Datatype definition AND any well_typed_* definition for constructor name mismatches. If well_typed_foo_def uses constructor X but the Datatype has Y, Cases_on will create impossible branches. Symptoms: msg ≠ 'string' goals from catch-all | _ => INR(TypeError 'string') branches. Fix: update well_typed_* definition to use correct Datatype constructor names.
works_when: Any proof that Cases_on's a type and then gvs's with a *rules* or *def* theorem that may use stale constructor names
evidence:
- source:semantics/prop/vyperTypeSystemScript.sml:93-96
- source:syntax/vyperASTScript.sml:60-63
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24333_t001

## L0893 scope='C4.1' tags=well_typed_binop,evaluate_binop,simp_vs_gvs
shape: well_typed_binop_no_type_error proof after Cases_on bop + gvs[well_typed_binop_def, is_*_inv, evaluate_type_def, AllCaseEqs()]
pattern: After initial gvs resolves types/values (~56 goals), use simp[evaluate_binop_def] NOT gvs[evaluate_binop_def, AllCaseEqs()] for the second pass. gvs+AllCaseEqs creates spurious case splits from TypeError catch-all branches producing unprovable msg≠'binop' goals. simp expands evaluate_binop_def correctly since the concrete value constructors match. For Div/Mod/Exp/UnsafeDiv: use rpt (COND_CASES_TAC >> simp[]) to handle zero-divisor guards. bounded_int_op/decimal_op/wrapped_int_op are already [local,simp] so they auto-close.
works_when: After well_typed_binop_def fix (UAdd->UnsafeAdd etc.) is applied, this pattern closes all 56 goals
evidence:
- tool_output:TO_type_system_rewrite-20260516T153850Z_m24333_t001
