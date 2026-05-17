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

## L0365 scope='global' tags=API,corruption,conjunction,workaround
shape: Writing HOL4 conjunction /\ in tool call content parameters
pattern: The Anthropic API consistently corrupts /\ by stripping the backslash when it appears in replace_text/edit_lines/write_file content parameters. Produces /@, /&e, /&#92; etc. Workarounds: (1) Avoid /\ in new theorem statements entirely - use nested implications, separate single-existential theorems, or inline proof. (2) Use mp_tac + simp[definition] + strip_tac to expand definitions in goal position, getting clean Skolemized witnesses without writing /\ to file. (3) For existing theorems, copy /\ from working parts of existing file content (pre-existing /\ survives because it was written before this API limitation).
works_when: Need to write HOL4 term quotations containing /\ conjunction to .sml files via tool calls
evidence:
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11333_t001
- tool_output:TO_type_system_rewrite-20260515T192259Z_m11275_t001

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

## L0434 scope='C4' tags=assign_target_sound_mutual,corollary,EVERY,arg_order
shape: Projecting no_type_error_result from assign_target_sound_mutual cj 1/cj 2
pattern: Use imp_res_tac (cj N assign_target_sound_mutual) >> gvs[] to project no_type_error_result from C3. For EVERY premises, the arg order is assign_target_assignable_context cx gv st (NOT cx st gv). Use EVERY (\gv. assign_target_assignable_context cx gv st) gvs matching C3 line 2290 exactly. For update/append wrappers, build assign_operation_runtime_typed from component facts first (well_typed_binop+value_runtime_typed for Update; evaluate_type+value_has_type for AppendOp).
works_when: Proving C4 wrapper theorems as projections from C3 assign_target_sound_mutual
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:313-376
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2274-2291

## L0437 scope='C4' tags=EVERY,arg_order,assign_target_assignable_context
shape: EVERY for assign_target_assignable_context must use lambda form
pattern: assign_target_assignable_context takes args (cx, gv, st) in that order. EVERY (assign_target_assignable_context cx st) gvs is WRONG type error because cx st is not a valid prefix - st is evaluation_state not assignment_value. Must use EVERY (\gv. assign_target_assignable_context cx gv st) gvs matching C3 line 2290. Both \ syntax and lambda character work in HOL4 definitions.
works_when: Writing theorem statements with EVERY over assign_target_assignable_context
evidence:
- source:semantics/prop/vyperTypeAssignSoundnessScript.sml:333
- source:semantics/prop/vyperTypeStatePreservationScript.sml:2290

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
